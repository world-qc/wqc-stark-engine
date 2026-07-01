//! Leaf proof parsing helpers (v1 / v2 transcripts).

use crate::transcript::{V1_MARKER, V2_MARKER};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedLeafBinding {
    pub sub_task_id: String,
    pub circuit_id: String,
    pub node_id: String,
    pub slice_id: String,
    pub output_hash: String,
    /// Optional v2 unitary↔Born link digest (empty when unbound).
    pub terminal_statevector_digest: String,
}

fn read_cstr(proof: &[u8], offset: usize) -> Option<(String, usize)> {
    let tail = proof.get(offset..)?;
    let end_rel = tail.iter().position(|&b| b == 0)?;
    let end = offset + end_rel;
    let value = std::str::from_utf8(&proof[offset..end]).ok()?;
    Some((value.to_string(), end + 1))
}

fn try_read_hex_digest(proof: &[u8], offset: usize) -> Option<(String, usize)> {
    let tail = proof.get(offset..)?;
    if tail.len() < 65 || tail[64] != 0 {
        return None;
    }
    let candidate = std::str::from_utf8(&tail[..64]).ok()?;
    if candidate.chars().all(|c| c.is_ascii_hexdigit()) {
        Some((candidate.to_string(), offset + 65))
    } else {
        None
    }
}

fn locate_leaf_marker(proof: &[u8]) -> Option<(usize, &'static [u8])> {
    for marker in [V1_MARKER, V2_MARKER] {
        if let Some(pos) = proof.windows(marker.len()).position(|w| w == marker) {
            return Some((pos, marker));
        }
    }
    None
}

/// Extracts public-input binding fields from a v1/v2 leaf transcript.
pub fn parse_leaf_binding(proof: &[u8]) -> Option<ParsedLeafBinding> {
    let (marker_pos, marker) = locate_leaf_marker(proof)?;
    let sub_task_id = std::str::from_utf8(&proof[..marker_pos]).ok()?.to_string();
    let cursor = marker_pos + marker.len();
    let (circuit_id, cursor) = read_cstr(proof, cursor)?;
    let (node_id, cursor) = read_cstr(proof, cursor)?;
    let (slice_id, cursor) = read_cstr(proof, cursor)?;
    let (output_hash, cursor) = read_cstr(proof, cursor)?;
    let terminal_statevector_digest = if marker == V2_MARKER {
        try_read_hex_digest(proof, cursor)
            .map(|(digest, _)| digest)
            .unwrap_or_default()
    } else {
        String::new()
    };
    Some(ParsedLeafBinding {
        sub_task_id,
        circuit_id,
        node_id,
        slice_id,
        output_hash,
        terminal_statevector_digest,
    })
}

pub fn parsed_to_stark_context<'a>(
    binding: &'a ParsedLeafBinding,
) -> crate::transcript::StarkContext<'a> {
    crate::transcript::StarkContext {
        circuit_id: &binding.circuit_id,
        sub_task_id: &binding.sub_task_id,
        node_id: &binding.node_id,
        slice_id: &binding.slice_id,
        output_hash: &binding.output_hash,
        terminal_statevector_digest: &binding.terminal_statevector_digest,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{generate_stark_proof, transcript::StarkContext};

    #[test]
    fn parse_generated_v1_leaf() {
        let ctx = StarkContext {
            circuit_id: "c1",
            sub_task_id: "sub-abc",
            node_id: "node-1",
            slice_id: "000",
            output_hash: "hash-out",
            terminal_statevector_digest: "",
        };
        let trace = crate::trace_spec::idle_qubit0_trace();
        let proof = generate_stark_proof(&ctx, &trace);
        let parsed = parse_leaf_binding(&proof).expect("parse");
        assert_eq!(parsed.sub_task_id, "sub-abc");
        assert_eq!(parsed.circuit_id, "c1");
        assert_eq!(parsed.slice_id, "000");
    }
}
