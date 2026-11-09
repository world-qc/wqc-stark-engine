//! Non-primitive operations: the circuit-side plugins and executor, and the prover-side
//! preprocessor, table provers and AIR builders.

use std::any::Any;

use crate::digest::*;
use crate::exec::*;
use crate::tables::*;
use crate::{Cfg, EF, F};
use p3_circuit::builder::{NonPrimitiveOperationData, NpoCircuitPlugin, NpoLoweringContext};
use p3_circuit::ops::{
    ExecutionContext, NonPrimitiveExecutor, NonPrimitivePreprocessedMap, NpoConfig, NpoTypeId, Op,
    OpStateMap,
};
use p3_circuit::tables::{NonPrimitiveTrace, TraceGeneratorFn, Traces};
use p3_circuit::{
    CircuitBuilderError, CircuitError, PreprocessedColumns, PreprocessedWriter, WitnessId,
};
use p3_circuit_prover::common::{BuiltNpoTable, CircuitTableAir, NpoAirBuilder, NpoPreprocessor};
use p3_circuit_prover::{
    AirVariant, BatchTableInstance, ConstraintProfile, DynamicAirEntry, NonPrimitiveTableEntry,
    NpoRelation, TablePacking, TableProver,
};
use p3_field::extension::BinomialExtensionField;
use p3_field::{PrimeCharacteristicRing, PrimeField64};

pub const GATE_OP: &str = "wqc/gate";
/// The second and third gate tables (see [`GATE_CHUNKS`]); the first is [`GATE_OP`].
pub const GATE_CHUNK_OPS: [&str; GATE_CHUNKS] = [GATE_OP, "wqc/gate1", "wqc/gate2"];
// `ALL`, `gate_chunk_plugins` and these generators are written out for three gate tables.
const _: () = assert!(GATE_CHUNKS == 3);
const GATE_TRACES: [TraceGeneratorFn<EF>; GATE_CHUNKS] = [gate_trace, gate1_trace, gate2_trace];
pub const BOUNDARY_OP: &str = "wqc/boundary";
pub const RANGE_OP: &str = "wqc/range";

pub fn gate_type() -> NpoTypeId {
    NpoTypeId::new(GATE_OP)
}
pub fn gate_chunk_type(c: usize) -> NpoTypeId {
    NpoTypeId::new(GATE_CHUNK_OPS[c])
}
pub fn boundary_type() -> NpoTypeId {
    NpoTypeId::new(BOUNDARY_OP)
}
pub fn range_type() -> NpoTypeId {
    NpoTypeId::new(RANGE_OP)
}
pub const DIGEST_OP: &str = "wqc/digest";
pub const PERM_OP: &str = "wqc/perm";
pub fn digest_type() -> NpoTypeId {
    NpoTypeId::new(DIGEST_OP)
}
pub fn perm_type() -> NpoTypeId {
    NpoTypeId::new(PERM_OP)
}

/// The gate op's execution state. `Default` (with `n = 0`) is only the framework's placeholder
/// before execution; the trace generators read a state the executor filled (`n ≥ 1`).
#[derive(Debug, Default)]
pub struct SvState {
    pub n: usize,
    pub steps: usize,
    pub rows: Vec<PairRow>,
    /// Final stored vector, by stored position (the boundary table reads it).
    pub fin: Vec<C>,
    /// Final logical state the digest table hashes: `fin` through the plan's frame, unless
    /// tampered.
    pub hashed: Vec<C>,
    pub sponge_in: Vec<[F; PW]>,
    pub sponge_out: Vec<[F; PW]>,
}

#[derive(Clone, Debug)]
pub struct SvExecutor {
    pub n: usize,
    pub gates: Vec<Gate>,
    pub(crate) tamper: Tamper,
}

impl NonPrimitiveExecutor<EF> for SvExecutor {
    fn execute(
        &self,
        _inputs: &[Vec<WitnessId>],
        outputs: &[Vec<WitnessId>],
        ctx: &mut ExecutionContext<'_, EF>,
    ) -> Result<(), CircuitError> {
        let plan = plan(self.n, &self.gates);
        let (mut rows, mut fin) = run(self.n, &plan);
        apply_tamper(self.tamper, &mut rows, &mut fin, plan.steps);
        let mut hashed = plan.frame.logical(&fin);
        if self.tamper == Tamper::DigestSwap {
            hashed[2].0 += 3;
        }
        let (sponge_in, sponge_out, digest) = sponge(&hashed);
        for (k, &wid) in outputs[0].iter().enumerate() {
            ctx.set_witness(wid, digest[k])?;
        }
        let st = ctx.get_op_state_mut::<SvState>(&gate_type());
        *st = SvState {
            n: self.n,
            steps: plan.steps,
            rows,
            fin,
            hashed,
            sponge_in,
            sponge_out,
        };
        Ok(())
    }
    fn op_type(&self) -> &NpoTypeId {
        static T: std::sync::OnceLock<NpoTypeId> = std::sync::OnceLock::new();
        T.get_or_init(gate_type)
    }
    fn preprocess(
        &self,
        _inputs: &[Vec<WitnessId>],
        outputs: &[Vec<WitnessId>],
        pw: &mut dyn PreprocessedWriter<EF>,
    ) -> Result<(), CircuitError> {
        let plan = plan(self.n, &self.gates);
        let mut gate = Vec::new();
        for r in &plan.rows {
            gate.extend([
                EF::ONE,
                EF::from_usize(r.t),
                EF::from_usize(r.i),
                EF::from_usize(r.j),
                EF::from_bool(r.active),
            ]);
            for (re, im) in r.m {
                gate.extend([fi::<EF>(re), fi::<EF>(im)]);
            }
        }
        // The first gate table always exists (it is this op's); the others only when they
        // have rows, so a circuit pays for no empty table.
        for (c, chunk) in split_rows(self.n, plan.steps, GP, &gate)
            .into_iter()
            .enumerate()
        {
            if c == 0 || !chunk.is_empty() {
                pw.register_non_primitive_preprocessed_no_read(&gate_chunk_type(c), chunk);
            }
        }
        // One row per stored position: its initial value, the step of its final read, and the
        // logical index and phase the final frame gives it.
        let mut boundary = Vec::new();
        for (s, (logical, phase)) in plan.frame.inverse().into_iter().enumerate() {
            let (c, d) = rot((1, 0), phase);
            boundary.extend([
                EF::ONE,
                EF::from_usize(s),
                if s == 0 { fi::<EF>(S) } else { EF::ZERO },
                EF::from_usize(plan.steps),
                EF::from_usize(logical),
                fi::<EF>(c),
                fi::<EF>(d),
            ]);
        }
        pw.register_non_primitive_preprocessed_no_read(&boundary_type(), &boundary);
        let range: Vec<EF> = (0..1usize << LOG_RANGE).map(EF::from_usize).collect();
        pw.register_non_primitive_preprocessed_no_read(&range_type(), &range);
        // Digest rows: the last one creates the digest witnesses (multiplicity set later).
        let blocks = (1usize << self.n) / 2;
        for k in 0..blocks {
            let last = k + 1 == blocks;
            pw.register_non_primitive_preprocessed_no_read(
                &digest_type(),
                &[EF::ONE, EF::from_bool(last), EF::from_usize(2 * k)],
            );
            for &wid in outputs[0].iter().take(DIGEST_LEN) {
                if last {
                    pw.register_non_primitive_output_index(&digest_type(), &[wid]);
                    pw.register_non_primitive_preprocessed_no_read(&digest_type(), &[EF::ZERO]);
                } else {
                    pw.register_non_primitive_preprocessed_no_read(
                        &digest_type(),
                        &[EF::ZERO, EF::ZERO],
                    );
                }
            }
        }
        pw.register_non_primitive_preprocessed_no_read(&perm_type(), &vec![EF::ONE; blocks]);
        Ok(())
    }
    fn num_exposed_outputs(&self) -> Option<usize> {
        Some(DIGEST_LEN)
    }
    fn boxed(&self) -> Box<dyn NonPrimitiveExecutor<EF>> {
        Box::new(self.clone())
    }
}

/// The logical traces, all derived from the gate op's execution state.
#[derive(Clone)]
pub enum SvTrace {
    Gate(usize, Vec<PairRow>),
    Boundary(Vec<C>),
    Range(Vec<u64>),
    Digest {
        hashed: Vec<C>,
        ins: Vec<[F; PW]>,
        outs: Vec<[F; PW]>,
    },
    Perm(Vec<[F; PW]>),
}

impl<T> NonPrimitiveTrace<T> for SvTrace {
    fn op_type(&self) -> NpoTypeId {
        match self {
            Self::Gate(c, _) => gate_chunk_type(*c),
            Self::Boundary(_) => boundary_type(),
            Self::Range(_) => range_type(),
            Self::Digest { .. } => digest_type(),
            Self::Perm(_) => perm_type(),
        }
    }
    fn rows(&self) -> usize {
        match self {
            Self::Gate(_, r) => r.len(),
            Self::Boundary(f) => f.len(),
            Self::Range(_) => 1 << LOG_RANGE,
            Self::Digest { ins, .. } => ins.len(),
            Self::Perm(i) => i.len(),
        }
    }
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn boxed_clone(&self) -> Box<dyn NonPrimitiveTrace<T>> {
        Box::new(self.clone())
    }
}

pub(crate) fn state(op_states: &OpStateMap) -> Option<&SvState> {
    op_states.get(&gate_type())?.downcast_ref::<SvState>()
}

fn gate_chunk_trace(
    op_states: &OpStateMap,
    c: usize,
) -> Result<Option<Box<dyn NonPrimitiveTrace<EF>>>, CircuitError> {
    let Some(s) = state(op_states) else {
        return Ok(None);
    };
    let rows = split_rows(s.n, s.steps, 1, &s.rows)[c].to_vec();
    if c > 0 && rows.is_empty() {
        return Ok(None);
    }
    Ok(Some(Box::new(SvTrace::Gate(c, rows))))
}
pub(crate) fn gate_trace(
    op_states: &OpStateMap,
) -> Result<Option<Box<dyn NonPrimitiveTrace<EF>>>, CircuitError> {
    gate_chunk_trace(op_states, 0)
}
pub(crate) fn gate1_trace(
    op_states: &OpStateMap,
) -> Result<Option<Box<dyn NonPrimitiveTrace<EF>>>, CircuitError> {
    gate_chunk_trace(op_states, 1)
}
pub(crate) fn gate2_trace(
    op_states: &OpStateMap,
) -> Result<Option<Box<dyn NonPrimitiveTrace<EF>>>, CircuitError> {
    gate_chunk_trace(op_states, 2)
}
pub(crate) fn boundary_trace(
    op_states: &OpStateMap,
) -> Result<Option<Box<dyn NonPrimitiveTrace<EF>>>, CircuitError> {
    Ok(state(op_states)
        .map(|s| Box::new(SvTrace::Boundary(s.fin.clone())) as Box<dyn NonPrimitiveTrace<EF>>))
}
pub(crate) fn range_trace(
    op_states: &OpStateMap,
) -> Result<Option<Box<dyn NonPrimitiveTrace<EF>>>, CircuitError> {
    Ok(state(op_states).map(|s| {
        Box::new(SvTrace::Range(range_queries(&s.rows))) as Box<dyn NonPrimitiveTrace<EF>>
    }))
}

pub(crate) fn digest_trace(
    op_states: &OpStateMap,
) -> Result<Option<Box<dyn NonPrimitiveTrace<EF>>>, CircuitError> {
    Ok(state(op_states).map(|s| {
        Box::new(SvTrace::Digest {
            hashed: s.hashed.clone(),
            ins: s.sponge_in.clone(),
            outs: s.sponge_out.clone(),
        }) as Box<dyn NonPrimitiveTrace<EF>>
    }))
}
pub(crate) fn perm_trace_gen(
    op_states: &OpStateMap,
) -> Result<Option<Box<dyn NonPrimitiveTrace<EF>>>, CircuitError> {
    Ok(state(op_states)
        .map(|s| Box::new(SvTrace::Perm(s.sponge_in.clone())) as Box<dyn NonPrimitiveTrace<EF>>))
}

pub struct SvGatePlugin {
    pub n: usize,
    pub gates: Vec<Gate>,
    pub(crate) tamper: Tamper,
}

impl NpoCircuitPlugin<EF> for SvGatePlugin {
    fn type_id(&self) -> NpoTypeId {
        gate_type()
    }
    fn lower(
        &self,
        data: &NonPrimitiveOperationData<EF>,
        out: &[(u32, p3_circuit::types::ExprId)],
        ctx: &mut NpoLoweringContext<'_, EF>,
    ) -> Result<Op<EF>, CircuitBuilderError> {
        for (_, e) in out {
            ctx.ensure_witness_id(*e);
        }
        let wids = out
            .iter()
            .map(|(_, e)| ctx.resolve_witness_id(*e, || "sv digest".into()))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Op::NonPrimitiveOpWithExecutor {
            inputs: vec![],
            outputs: vec![wids],
            executor: Box::new(SvExecutor {
                n: self.n,
                gates: self.gates.clone(),
                tamper: self.tamper,
            }),
            op_id: data.op_id,
        })
    }
    fn trace_generator(&self) -> TraceGeneratorFn<EF> {
        gate_trace
    }
    fn config(&self) -> NpoConfig {
        NpoConfig::new(())
    }
}

/// Registers a trace generator for a table that `wqc/gate` populates; never lowered.
pub struct SvSidePlugin(pub NpoTypeId, pub TraceGeneratorFn<EF>);

impl NpoCircuitPlugin<EF> for SvSidePlugin {
    fn type_id(&self) -> NpoTypeId {
        self.0.clone()
    }
    fn lower(
        &self,
        data: &NonPrimitiveOperationData<EF>,
        _: &[(u32, p3_circuit::types::ExprId)],
        _: &mut NpoLoweringContext<'_, EF>,
    ) -> Result<Op<EF>, CircuitBuilderError> {
        Err(CircuitBuilderError::InvalidNonPrimitiveOpConfiguration {
            op: data.op_type.clone(),
        })
    }
    fn trace_generator(&self) -> TraceGeneratorFn<EF> {
        self.1
    }
    fn config(&self) -> NpoConfig {
        NpoConfig::new(())
    }
}

/// The gate tables after the first, which the gate op's trace fills.
pub fn gate_chunk_plugins() -> [SvSidePlugin; GATE_CHUNKS - 1] {
    [
        SvSidePlugin(gate_chunk_type(1), GATE_TRACES[1]),
        SvSidePlugin(gate_chunk_type(2), GATE_TRACES[2]),
    ]
}
pub fn boundary_plugin() -> SvSidePlugin {
    SvSidePlugin(boundary_type(), boundary_trace)
}
pub fn range_plugin() -> SvSidePlugin {
    SvSidePlugin(range_type(), range_trace)
}
pub fn digest_plugin() -> SvSidePlugin {
    SvSidePlugin(digest_type(), digest_trace)
}
pub fn perm_plugin() -> SvSidePlugin {
    SvSidePlugin(perm_type(), perm_trace_gen)
}

pub struct SvPreprocessor;

impl NpoPreprocessor<F> for SvPreprocessor {
    fn preprocess(
        &self,
        _circuit: &dyn Any,
        preprocessed: &mut dyn Any,
    ) -> Result<NonPrimitivePreprocessedMap<F>, CircuitError> {
        let mut out = NonPrimitivePreprocessedMap::default();
        let Some(prep) = preprocessed.downcast_mut::<PreprocessedColumns<EF, 1>>() else {
            return Ok(out);
        };
        let types = (0..GATE_CHUNKS).map(gate_chunk_type).chain([
            boundary_type(),
            range_type(),
            perm_type(),
        ]);
        for ty in types {
            if let Some(v) = prep.non_primitive.get(&ty) {
                out.insert(ty, v.clone());
            }
        }
        if let Some(v) = prep.non_primitive.get(&digest_type()) {
            let mut v = v.clone();
            let dups = prep.dup_npo_outputs.get(&digest_type());
            for row in v.chunks_mut(DP) {
                if row[1] != F::ONE {
                    continue;
                }
                for c in 0..DIGEST_LEN {
                    let wid = row[3 + 2 * c].as_canonical_u64() as usize;
                    let dup = dups.and_then(|d| d.get(wid).copied()).unwrap_or(false);
                    row[4 + 2 * c] = if dup {
                        -F::ONE
                    } else {
                        F::from_u32(prep.ext_reads.get(wid).copied().unwrap_or(0))
                    };
                }
            }
            out.insert(digest_type(), v);
        }
        Ok(out)
    }
}

#[derive(Clone, Copy)]
pub enum SvTable {
    /// Gate table `c` of [`GATE_CHUNKS`].
    Gate(usize),
    Boundary,
    Range,
    Digest,
    Perm,
}

impl SvTable {
    /// Every table, in prover registration order. The gate tables are listed one by one, as
    /// are [`gate_chunk_plugins`] and the `gate*_trace` generators: changing [`GATE_CHUNKS`]
    /// means updating all three (the assertions below catch a mismatch in count).
    pub const ALL: [Self; GATE_CHUNKS + 4] = [
        Self::Gate(0),
        Self::Gate(1),
        Self::Gate(2),
        Self::Boundary,
        Self::Range,
        Self::Digest,
        Self::Perm,
    ];
    pub fn op_type(self) -> NpoTypeId {
        match self {
            Self::Gate(c) => gate_chunk_type(c),
            Self::Boundary => boundary_type(),
            Self::Range => range_type(),
            Self::Digest => digest_type(),
            Self::Perm => perm_type(),
        }
    }
    fn width(self) -> usize {
        match self {
            Self::Gate(_) => GP,
            Self::Boundary => BP,
            Self::Range => 1,
            Self::Digest => DP,
            Self::Perm => PP,
        }
    }
    pub fn from_op(op: &NpoTypeId) -> Option<Self> {
        Self::ALL.into_iter().find(|t| t.op_type() == *op)
    }
    fn air(self, prep: Vec<F>, min_height: usize) -> DynamicAirEntry<Cfg> {
        match self {
            Self::Gate(_) => DynamicAirEntry::new(Box::new(GateTableAir { prep, min_height })),
            Self::Boundary => DynamicAirEntry::new(Box::new(BoundaryTableAir { prep, min_height })),
            Self::Range => DynamicAirEntry::new(Box::new(RangeTableAir { prep, min_height })),
            Self::Digest => DynamicAirEntry::new(Box::new(DigestTableAir { prep, min_height })),
            Self::Perm => DynamicAirEntry::new(Box::new(PermTableAir::new(prep, min_height))),
        }
    }
    fn degree(self, prep_len: usize, min_height: usize) -> usize {
        padded_rows(prep_len / self.width(), min_height).trailing_zeros() as usize
    }
}

pub struct SvProver(pub SvTable);

impl TableProver<Cfg> for SvProver {
    fn op_type(&self) -> NpoTypeId {
        self.0.op_type()
    }
    fn batch_instance_with_committed_preprocessed(
        &self,
        _config: &Cfg,
        packing: &TablePacking,
        traces: &[(&NpoTypeId, &dyn Any)],
        committed: &[F],
        circuit_extension_degree: u32,
    ) -> Option<BatchTableInstance<Cfg>> {
        if circuit_extension_degree != 1 {
            return None;
        }
        let op = self.0.op_type();
        let trace = traces
            .iter()
            .find(|(id, _)| **id == op)?
            .1
            .downcast_ref::<SvTrace>()?;
        let min_height = packing.min_trace_height();
        let (air, matrix, rows) = match (self.0, trace) {
            (SvTable::Gate(c), SvTrace::Gate(tc, r)) if c == *tc => {
                let a = GateTableAir {
                    prep: committed.to_vec(),
                    min_height,
                };
                let m = a.main(r);
                (DynamicAirEntry::new(Box::new(a)), m, r.len())
            }
            (SvTable::Boundary, SvTrace::Boundary(f)) => {
                let a = BoundaryTableAir {
                    prep: committed.to_vec(),
                    min_height,
                };
                let m = a.main(f);
                (DynamicAirEntry::new(Box::new(a)), m, f.len())
            }
            (SvTable::Range, SvTrace::Range(q)) => {
                let a = RangeTableAir {
                    prep: committed.to_vec(),
                    min_height,
                };
                let m = a.main(q);
                (DynamicAirEntry::new(Box::new(a)), m, 1 << LOG_RANGE)
            }
            (SvTable::Digest, SvTrace::Digest { hashed, ins, outs }) => {
                let a = DigestTableAir {
                    prep: committed.to_vec(),
                    min_height,
                };
                let m = a.main(hashed, ins, outs);
                (DynamicAirEntry::new(Box::new(a)), m, ins.len())
            }
            (SvTable::Perm, SvTrace::Perm(ins)) => {
                let a = PermTableAir::new(committed.to_vec(), min_height);
                let m = a.main(ins);
                (DynamicAirEntry::new(Box::new(a)), m, ins.len())
            }
            _ => return None,
        };
        Some(BatchTableInstance {
            op_type: op,
            air,
            trace: matrix,
            public_values: Vec::new(),
            rows,
            lanes: 1,
        })
    }
    fn batch_instance_d1(
        &self,
        _: &Cfg,
        _: &TablePacking,
        _: &Traces<EF>,
    ) -> Option<BatchTableInstance<Cfg>> {
        None
    }
    fn batch_instance_d2(
        &self,
        _: &Cfg,
        _: &TablePacking,
        _: &Traces<BinomialExtensionField<F, 2>>,
    ) -> Option<BatchTableInstance<Cfg>> {
        None
    }
    fn batch_instance_d4(
        &self,
        _: &Cfg,
        _: &TablePacking,
        _: &Traces<BinomialExtensionField<F, 4>>,
    ) -> Option<BatchTableInstance<Cfg>> {
        None
    }
    fn batch_instance_d6(
        &self,
        _: &Cfg,
        _: &TablePacking,
        _: &Traces<BinomialExtensionField<F, 6>>,
    ) -> Option<BatchTableInstance<Cfg>> {
        None
    }
    fn batch_instance_d8(
        &self,
        _: &Cfg,
        _: &TablePacking,
        _: &Traces<BinomialExtensionField<F, 8>>,
    ) -> Option<BatchTableInstance<Cfg>> {
        None
    }
    fn batch_air_from_table_entry(
        &self,
        _: &Cfg,
        _: usize,
        _: u32,
        _: &NonPrimitiveTableEntry<Cfg>,
    ) -> Result<DynamicAirEntry<Cfg>, String> {
        Ok(self.0.air(Vec::new(), 1))
    }
    fn air_with_committed_preprocessed(
        &self,
        committed: Vec<F>,
        min_height: usize,
        _lanes: usize,
        _ext: u32,
    ) -> Option<DynamicAirEntry<Cfg>> {
        Some(self.0.air(committed, min_height))
    }
}

/// One builder per table: the framework builds at most one AIR per builder, and orders the
/// AIRs by builder registration (which must match the table prover order).
pub struct SvAirBuilder(pub SvTable);

impl NpoAirBuilder<Cfg, 1> for SvAirBuilder {
    fn try_build(
        &self,
        op_type: &NpoTypeId,
        prep: &[F],
        min_height: usize,
        _lanes: usize,
        _p: ConstraintProfile,
    ) -> Option<(CircuitTableAir<Cfg, 1>, usize)> {
        let t = SvTable::from_op(op_type).filter(|t| t.op_type() == self.0.op_type())?;
        Some((
            CircuitTableAir::Dynamic(t.air(prep.to_vec(), min_height)),
            t.degree(prep.len(), min_height),
        ))
    }
    fn try_build_trusted(
        &self,
        op_type: &NpoTypeId,
        prep: &[F],
        min_height: usize,
        lanes: usize,
        p: ConstraintProfile,
    ) -> Option<BuiltNpoTable<Cfg, 1>> {
        let t = SvTable::from_op(op_type)?;
        let built = self.try_build(op_type, prep, min_height, lanes, p)?;
        Some(BuiltNpoTable::new(
            built.0,
            built.1,
            NpoRelation::new(
                op_type.clone(),
                prep.len() / t.width(),
                lanes,
                AirVariant::Baseline,
                Vec::new(),
            ),
        ))
    }
}

pub fn air_builders() -> Vec<Box<dyn NpoAirBuilder<Cfg, 1>>> {
    SvTable::ALL
        .into_iter()
        .map(|t| Box::new(SvAirBuilder(t)) as Box<dyn NpoAirBuilder<Cfg, 1>>)
        .collect()
}

pub fn table_provers() -> Vec<Box<dyn TableProver<Cfg>>> {
    SvTable::ALL
        .into_iter()
        .map(|t| Box::new(SvProver(t)) as Box<dyn TableProver<Cfg>>)
        .collect()
}
