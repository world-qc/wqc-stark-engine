//! Non-primitive operations: the circuit-side plugins and executor, and the prover-side
//! preprocessor, table provers and AIR builders.

use std::any::Any;

use crate::born::*;
use crate::born_tables::*;
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
pub const WEIGHT_OP: &str = "wqc/weight";
pub const DRAW_OP: &str = "wqc/draw";
pub const PRF_OP: &str = "wqc/prf";
pub const COUNT_OP: &str = "wqc/count";
pub fn weight_type() -> NpoTypeId {
    NpoTypeId::new(WEIGHT_OP)
}
pub fn draw_type() -> NpoTypeId {
    NpoTypeId::new(DRAW_OP)
}
pub fn prf_type() -> NpoTypeId {
    NpoTypeId::new(PRF_OP)
}
pub fn count_type() -> NpoTypeId {
    NpoTypeId::new(COUNT_OP)
}

/// Digest words the op outputs: the state digest, then the counts digest when it samples.
pub(crate) fn outputs_len(sampling: bool) -> usize {
    if sampling {
        2 * DIGEST_LEN
    } else {
        DIGEST_LEN
    }
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
    pub born: Option<BornState>,
}

/// The sampling part of the execution state.
#[derive(Debug, Clone)]
pub struct BornState {
    pub seed: u64,
    /// The final logical state the weight table reads (from the boundary table's values).
    pub logical: Vec<C>,
    pub run: BornRun,
    /// Counts as the counts table reports them (the run's, unless tampered).
    pub counts: Vec<u64>,
    pub count_in: Vec<[F; PW]>,
    pub count_out: Vec<[F; PW]>,
}

#[derive(Clone, Debug)]
pub struct SvExecutor {
    pub n: usize,
    /// Already fused ([`fuse`]).
    pub gates: Vec<Gate>,
    pub sampling: Option<Sampling>,
    pub(crate) tamper: Tamper,
}

/// [`Tamper::DrawMove`]: credits the first accepted draw to the next basis state with weight.
fn move_draw(run: &mut BornRun, sampling: &Sampling) {
    let dim = run.hits.len();
    let k = run
        .draws
        .iter()
        .position(|d| d.live && d.accepted)
        .expect("a shot");
    let from = run.draws[k].b;
    let to = (1..dim)
        .map(|i| (from + i) % dim)
        .find(|&b| run.cum[b + 1] > run.cum[b])
        .expect("two states with weight");
    let d = &mut run.draws[k];
    d.b = to;
    d.lo = run.cum[to];
    d.hi = run.cum[to + 1];
    run.hits[from] -= 1;
    run.hits[to] += 1;
    run.counts[sampling.outcome(from)] -= 1;
    run.counts[sampling.outcome(to)] += 1;
}

impl SvExecutor {
    /// The sampling tables' preprocessed rows; returns the permutations they add.
    fn preprocess_sampling(
        &self,
        sampling: &Sampling,
        inputs: &[Vec<WitnessId>],
        outputs: &[Vec<WitnessId>],
        pw: &mut dyn PreprocessedWriter<EF>,
    ) -> Result<usize, CircuitError> {
        let dim = 1usize << self.n;
        for b in 0..dim {
            pw.register_non_primitive_preprocessed_no_read(
                &weight_type(),
                &[
                    EF::ONE,
                    EF::from_usize(b),
                    EF::from_usize(sampling.outcome(b)),
                    EF::from_bool(b + 1 == dim),
                ],
            );
        }
        // The first draw row reads seed_lo, seed_hi and shots from the statement.
        let shots = EF::from_u32(sampling.shots);
        for j in 0..sampling.draws() {
            pw.register_non_primitive_preprocessed_no_read(
                &draw_type(),
                &[EF::ONE, EF::from_usize(j), shots, EF::from_bool(j == 0)],
            );
            if j == 0 {
                pw.register_non_primitive_witness_reads(&draw_type(), &inputs[0])?;
            } else {
                pw.register_non_primitive_preprocessed_no_read(&draw_type(), &[EF::ZERO; 3]);
            }
        }
        let prfs = sampling.draws() / RATE;
        for k in 0..prfs {
            pw.register_non_primitive_preprocessed_no_read(
                &prf_type(),
                &[EF::ONE, EF::from_usize(k)],
            );
        }
        // Count rows: the last one creates the counts digest witnesses (multiplicity set later).
        let blocks = sampling.counts_len() / RATE;
        for k in 0..blocks {
            let last = k + 1 == blocks;
            pw.register_non_primitive_preprocessed_no_read(
                &count_type(),
                &[EF::ONE, EF::from_usize(RATE * k), EF::from_bool(last)],
            );
            for &wid in &outputs[0][DIGEST_LEN..] {
                if last {
                    pw.register_non_primitive_output_index(&count_type(), &[wid]);
                    pw.register_non_primitive_preprocessed_no_read(&count_type(), &[EF::ZERO]);
                } else {
                    pw.register_non_primitive_preprocessed_no_read(
                        &count_type(),
                        &[EF::ZERO, EF::ZERO],
                    );
                }
            }
        }
        Ok(prfs + blocks)
    }
}

impl NonPrimitiveExecutor<EF> for SvExecutor {
    fn execute(
        &self,
        inputs: &[Vec<WitnessId>],
        outputs: &[Vec<WitnessId>],
        ctx: &mut ExecutionContext<'_, EF>,
    ) -> Result<(), CircuitError> {
        let plan = plan_fused(self.n, &self.gates);
        let (mut rows, mut fin) = run(self.n, &plan);
        apply_tamper(self.tamper, &mut rows, &mut fin, plan.steps);
        let logical = plan.frame.logical(&fin);
        let born = match &self.sampling {
            Some(sampling) => {
                let word = |k: usize| -> Result<u64, CircuitError> {
                    Ok(ctx.get_witness(inputs[0][k])?.as_canonical_u64())
                };
                let (lo, hi) = (word(0)?, word(1)?);
                let fail = |expected: String| CircuitError::NonPrimitiveOpLayoutMismatch {
                    op: gate_type(),
                    expected,
                    got: 0,
                };
                if lo >> 32 != 0 || hi >> 32 != 0 {
                    return Err(fail("seed words below 2^32".into()));
                }
                let seed = lo | hi << 32;
                let mut run =
                    sample(&logical, sampling, seed).map_err(|e| fail(format!("{e:?}")))?;
                if self.tamper == Tamper::DrawMove {
                    move_draw(&mut run, sampling);
                }
                let mut counts = run.counts.clone();
                if self.tamper == Tamper::CountShift {
                    // Report one shot under another register value than it was drawn for.
                    let k = counts.iter().position(|&c| c > 0).expect("a shot");
                    counts[k] -= 1;
                    let len = counts.len();
                    counts[(k + 1) % len] += 1;
                }
                let (count_in, count_out, cdigest) = counts_sponge(&counts);
                for (k, &wid) in outputs[0][DIGEST_LEN..].iter().enumerate() {
                    ctx.set_witness(wid, cdigest[k])?;
                }
                Some(BornState {
                    seed,
                    logical,
                    run,
                    counts,
                    count_in,
                    count_out,
                })
            }
            None => None,
        };
        let mut hashed = plan.frame.logical(&fin);
        if self.tamper == Tamper::DigestSwap {
            hashed[2].0 += 3;
        }
        let (sponge_in, sponge_out, digest) = sponge(&hashed);
        for (k, &wid) in outputs[0].iter().take(DIGEST_LEN).enumerate() {
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
            born,
        };
        Ok(())
    }
    fn op_type(&self) -> &NpoTypeId {
        static T: std::sync::OnceLock<NpoTypeId> = std::sync::OnceLock::new();
        T.get_or_init(gate_type)
    }
    fn preprocess(
        &self,
        inputs: &[Vec<WitnessId>],
        outputs: &[Vec<WitnessId>],
        pw: &mut dyn PreprocessedWriter<EF>,
    ) -> Result<(), CircuitError> {
        let plan = plan_fused(self.n, &self.gates);
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
                EF::from_usize(1 + self.sampling.is_some() as usize),
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
        let mut perms = blocks;
        if let Some(sampling) = &self.sampling {
            perms += self.preprocess_sampling(sampling, inputs, outputs, pw)?;
        }
        pw.register_non_primitive_preprocessed_no_read(&perm_type(), &vec![EF::ONE; perms]);
        Ok(())
    }
    fn num_exposed_outputs(&self) -> Option<usize> {
        Some(outputs_len(self.sampling.is_some()))
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
    Weight(Box<BornState>),
    Draw(Box<BornState>),
    Prf(Box<BornState>),
    Count(Box<BornState>),
}

impl<T> NonPrimitiveTrace<T> for SvTrace {
    fn op_type(&self) -> NpoTypeId {
        match self {
            Self::Gate(c, _) => gate_chunk_type(*c),
            Self::Boundary(_) => boundary_type(),
            Self::Range(_) => range_type(),
            Self::Digest { .. } => digest_type(),
            Self::Perm(_) => perm_type(),
            Self::Weight(_) => weight_type(),
            Self::Draw(_) => draw_type(),
            Self::Prf(_) => prf_type(),
            Self::Count(_) => count_type(),
        }
    }
    fn rows(&self) -> usize {
        match self {
            Self::Gate(_, r) => r.len(),
            Self::Boundary(f) => f.len(),
            Self::Range(_) => 1 << LOG_RANGE,
            Self::Digest { ins, .. } => ins.len(),
            Self::Perm(i) => i.len(),
            Self::Weight(b) => b.logical.len(),
            Self::Draw(b) => b.run.draws.len(),
            Self::Prf(b) => b.run.prf_in.len(),
            Self::Count(b) => b.count_in.len(),
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
        let mut q = range_queries(&s.rows);
        if let Some(b) = &s.born {
            q.extend(draw_range_queries(&b.run.draws));
        }
        Box::new(SvTrace::Range(q)) as Box<dyn NonPrimitiveTrace<EF>>
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
    Ok(state(op_states).map(|s| {
        // In the order the preprocessing counted them: state digest, sampling, counts digest.
        let mut ins = s.sponge_in.clone();
        if let Some(b) = &s.born {
            ins.extend(&b.run.prf_in);
            ins.extend(&b.count_in);
        }
        Box::new(SvTrace::Perm(ins)) as Box<dyn NonPrimitiveTrace<EF>>
    }))
}

fn born_trace(
    op_states: &OpStateMap,
    wrap: fn(Box<BornState>) -> SvTrace,
) -> Result<Option<Box<dyn NonPrimitiveTrace<EF>>>, CircuitError> {
    Ok(state(op_states)
        .and_then(|s| s.born.clone())
        .map(|b| Box::new(wrap(Box::new(b))) as Box<dyn NonPrimitiveTrace<EF>>))
}
pub(crate) fn weight_trace(
    op_states: &OpStateMap,
) -> Result<Option<Box<dyn NonPrimitiveTrace<EF>>>, CircuitError> {
    born_trace(op_states, SvTrace::Weight)
}
pub(crate) fn draw_trace(
    op_states: &OpStateMap,
) -> Result<Option<Box<dyn NonPrimitiveTrace<EF>>>, CircuitError> {
    born_trace(op_states, SvTrace::Draw)
}
pub(crate) fn prf_trace(
    op_states: &OpStateMap,
) -> Result<Option<Box<dyn NonPrimitiveTrace<EF>>>, CircuitError> {
    born_trace(op_states, SvTrace::Prf)
}
pub(crate) fn count_trace(
    op_states: &OpStateMap,
) -> Result<Option<Box<dyn NonPrimitiveTrace<EF>>>, CircuitError> {
    born_trace(op_states, SvTrace::Count)
}

pub struct SvGatePlugin {
    pub n: usize,
    /// Already fused ([`fuse`]).
    pub gates: Vec<Gate>,
    pub sampling: Option<Sampling>,
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
        // Sampling reads seed_lo, seed_hi and shots from the statement.
        let inputs = data
            .input_exprs
            .iter()
            .map(|g| {
                g.iter()
                    .map(|&e| ctx.resolve_witness_id(e, || "sv sampling input".into()))
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Op::NonPrimitiveOpWithExecutor {
            inputs,
            outputs: vec![wids],
            executor: Box::new(SvExecutor {
                n: self.n,
                gates: self.gates.clone(),
                sampling: self.sampling.clone(),
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
/// The sampling tables; they have rows only when the leaf samples.
pub fn sampling_plugins() -> [SvSidePlugin; 4] {
    [
        SvSidePlugin(weight_type(), weight_trace),
        SvSidePlugin(draw_type(), draw_trace),
        SvSidePlugin(prf_type(), prf_trace),
        SvSidePlugin(count_type(), count_trace),
    ]
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
            weight_type(),
            draw_type(),
            prf_type(),
        ]);
        for ty in types {
            if let Some(v) = prep.non_primitive.get(&ty) {
                out.insert(ty, v.clone());
            }
        }
        // The digest and counts tables' last rows create output witnesses: each gets the number
        // of reads as its multiplicity, or −1 if another op already created it.
        for (ty, width, last_col) in [(digest_type(), DP, 1), (count_type(), CP, 2)] {
            let Some(v) = prep.non_primitive.get(&ty) else {
                continue;
            };
            let mut v = v.clone();
            let dups = prep.dup_npo_outputs.get(&gate_type());
            for row in v.chunks_mut(width) {
                if row[last_col] != F::ONE {
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
            out.insert(ty, v);
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
    Weight,
    Draw,
    Prf,
    Count,
}

impl SvTable {
    /// Every table, in prover registration order. The gate tables are listed one by one, as
    /// are [`gate_chunk_plugins`] and the `gate*_trace` generators: changing [`GATE_CHUNKS`]
    /// means updating all three (the assertions below catch a mismatch in count).
    pub const ALL: [Self; GATE_CHUNKS + 8] = [
        Self::Gate(0),
        Self::Gate(1),
        Self::Gate(2),
        Self::Boundary,
        Self::Range,
        Self::Digest,
        Self::Perm,
        Self::Weight,
        Self::Draw,
        Self::Prf,
        Self::Count,
    ];
    pub fn op_type(self) -> NpoTypeId {
        match self {
            Self::Gate(c) => gate_chunk_type(c),
            Self::Boundary => boundary_type(),
            Self::Range => range_type(),
            Self::Digest => digest_type(),
            Self::Perm => perm_type(),
            Self::Weight => weight_type(),
            Self::Draw => draw_type(),
            Self::Prf => prf_type(),
            Self::Count => count_type(),
        }
    }
    fn width(self) -> usize {
        match self {
            Self::Gate(_) => GP,
            Self::Boundary => BP,
            Self::Range => 1,
            Self::Digest => DP,
            Self::Perm => PP,
            Self::Weight => WP,
            Self::Draw => RP,
            Self::Prf => FP,
            Self::Count => CP,
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
            Self::Weight => DynamicAirEntry::new(Box::new(WeightTableAir { prep, min_height })),
            Self::Draw => DynamicAirEntry::new(Box::new(DrawTableAir { prep, min_height })),
            Self::Prf => DynamicAirEntry::new(Box::new(PrfTableAir { prep, min_height })),
            Self::Count => DynamicAirEntry::new(Box::new(CountTableAir { prep, min_height })),
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
            (SvTable::Weight, SvTrace::Weight(b)) => {
                let a = WeightTableAir {
                    prep: committed.to_vec(),
                    min_height,
                };
                let m = a.main(&b.logical, &b.run);
                (DynamicAirEntry::new(Box::new(a)), m, b.logical.len())
            }
            (SvTable::Draw, SvTrace::Draw(b)) => {
                let a = DrawTableAir {
                    prep: committed.to_vec(),
                    min_height,
                };
                let m = a.main(b.seed, &b.run);
                (DynamicAirEntry::new(Box::new(a)), m, b.run.draws.len())
            }
            (SvTable::Prf, SvTrace::Prf(b)) => {
                let a = PrfTableAir {
                    prep: committed.to_vec(),
                    min_height,
                };
                let m = a.main(&b.run);
                (DynamicAirEntry::new(Box::new(a)), m, b.run.prf_in.len())
            }
            (SvTable::Count, SvTrace::Count(b)) => {
                let a = CountTableAir {
                    prep: committed.to_vec(),
                    min_height,
                };
                let m = a.main(&b.counts, &b.count_in, &b.count_out);
                (DynamicAirEntry::new(Box::new(a)), m, b.count_in.len())
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
