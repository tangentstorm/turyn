/// Measure the size of a 16-way decision trie for boundary configs.
///
/// The trie interleaves all four sequences (X,Y,Z,W) at each boundary position,
/// visited in bouncing order: 0, 2k-1, 1, 2k-2, 2, 2k-3, ...
/// This means after placing t pairs of positions, t lag constraints are fully
/// determined and can prune dead branches.
///
/// Each node has 16 children (one per sign column: x,y,z,w each ±1).
/// Encoding: x=bit0, y=bit1, z=bit2, w=bit3 (0=−1, 1=+1).
/// Children[i] = 0 means no valid completion for that sign column.

use std::collections::HashMap;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let k: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(7);

    eprintln!("Building decision trie for k={} (valid for all n >= {})", k, 2 * k);

    // Bouncing position order: 0, 2k-1, 1, 2k-2, 2, 2k-3, ...
    let mut pos_order: Vec<usize> = Vec::with_capacity(2 * k);
    for t in 0..k {
        pos_order.push(t);          // prefix position
        pos_order.push(2 * k - 1 - t); // suffix position
    }
    eprintln!("Position order: {:?}", pos_order);

    // Build exact-lag bit pairs (same math as gen_table).
    // Lag index j (0..k): absolute lag s = n-k+j for any n >= 2k.
    // X/Y/Z (length n): pairs (i, k+i+j) for i = 0..k-j-1
    // W (length n-1): pairs (i, k+i+j+1) for i = 0..k-j-2 (only when j < k-1)
    struct ExactLag {
        xy_pairs: Vec<(usize, usize)>,
        z_pairs: Vec<(usize, usize)>,
        w_pairs: Vec<(usize, usize)>,
    }
    let mut exact_lags: Vec<ExactLag> = Vec::new();
    for j in 0..k {
        let xy_pairs: Vec<(usize, usize)> = (0..k - j)
            .map(|i| (i, k + i + j))
            .collect();
        let z_pairs = xy_pairs.clone();
        let w_pairs: Vec<(usize, usize)> = if j < k - 1 {
            (0..k - j - 1).map(|i| (i, k + i + j + 1)).collect()
        } else {
            Vec::new()
        };
        exact_lags.push(ExactLag { xy_pairs, z_pairs, w_pairs });
    }

    // Which lags become fully determined after placing positions 0..depth-1 in pos_order?
    // A lag is fully determined when ALL its pair positions have been placed.
    let mut lags_complete_at_depth: Vec<Vec<usize>> = vec![Vec::new(); 2 * k + 1];
    for (lag_idx, lag) in exact_lags.iter().enumerate() {
        // Collect all positions involved in this lag (across all 4 sequences, but
        // boundary positions are the same indices for X/Y/Z; W uses different pairs)
        let mut all_positions = std::collections::HashSet::new();
        for &(a, b) in &lag.xy_pairs {
            all_positions.insert(a);
            all_positions.insert(b);
        }
        // Z pairs are same as XY
        // W pairs may differ
        for &(a, b) in &lag.w_pairs {
            all_positions.insert(a);
            all_positions.insert(b);
        }

        // Find the earliest depth at which all these positions have been placed
        let mut max_depth = 0;
        for &pos in &all_positions {
            let depth = pos_order.iter().position(|&p| p == pos).unwrap();
            max_depth = max_depth.max(depth);
        }
        lags_complete_at_depth[max_depth + 1].push(lag_idx);
    }

    for d in 0..=2 * k {
        if !lags_complete_at_depth[d].is_empty() {
            eprintln!("  After depth {}: lags {:?} fully determined", d, lags_complete_at_depth[d]);
        }
    }

    // Build the trie by DFS enumeration.
    // State: partial assignment of x,y,z,w bits at boundary positions.
    // At each depth, try all 16 sign columns, check if any newly-completed lag
    // constraints are satisfied, and recurse.

    let depth = 2 * k;
    // Trie nodes: Vec of [u32; 16]. nodes[0] is the root.
    // Children are node IDs; 0 = dead end (no valid completion).
    // We use a HashMap to deduplicate identical subtrees.
    let mut nodes: Vec<[u32; 16]> = Vec::new();
    nodes.push([0u32; 16]); // node 0 is the "dead" sentinel
    nodes.push([0u32; 16]); // node 1 is the root (filled in by build)

    // For deduplication: map from child array → node_id
    let mut dedup: HashMap<[u32; 16], u32> = HashMap::new();
    dedup.insert([0u32; 16], 0); // dead node

    // Recursive build. Returns a node_id.
    // bits_x, bits_y, bits_z, bits_w: partial boundary bit patterns
    struct BuildCtx {
        pos_order: Vec<usize>,
        exact_lags: Vec<(Vec<(usize, usize)>, Vec<(usize, usize)>, Vec<(usize, usize)>)>,
        lags_complete_at_depth: Vec<Vec<usize>>,
        k: usize,
    }

    let ctx = BuildCtx {
        pos_order: pos_order.clone(),
        exact_lags: exact_lags.iter().map(|el| (el.xy_pairs.clone(), el.z_pairs.clone(), el.w_pairs.clone())).collect(),
        lags_complete_at_depth: lags_complete_at_depth.clone(),
        k,
    };

    fn bnd_autocorr(bits: u32, pairs: &[(usize, usize)]) -> i32 {
        let mut val = 0i32;
        for &(bi, bj) in pairs {
            val += 1 - 2 * (((bits >> bi) ^ (bits >> bj)) & 1) as i32;
        }
        val
    }

    fn check_lags(xb: u32, yb: u32, zb: u32, wb: u32, lag_indices: &[usize], ctx: &BuildCtx) -> bool {
        for &li in lag_indices {
            let (ref xy_pairs, ref z_pairs, ref w_pairs) = ctx.exact_lags[li];
            let nx = bnd_autocorr(xb, xy_pairs);
            let ny = bnd_autocorr(yb, xy_pairs);
            let nz = bnd_autocorr(zb, z_pairs);
            let nw = bnd_autocorr(wb, w_pairs);
            if nx + ny + 2 * nz + 2 * nw != 0 {
                return false;
            }
        }
        true
    }

    // Count leaves for stats
    let mut leaf_count: u64 = 0;

    fn build(
        d: usize, xb: u32, yb: u32, zb: u32, wb: u32,
        ctx: &BuildCtx,
        nodes: &mut Vec<[u32; 16]>,
        dedup: &mut HashMap<[u32; 16], u32>,
        leaf_count: &mut u64,
    ) -> u32 {
        let depth = 2 * ctx.k;
        if d == depth {
            // Leaf: all positions assigned, all lags satisfied (checked incrementally)
            *leaf_count += 1;
            return u32::MAX; // special leaf marker
        }

        let pos = ctx.pos_order[d];
        let mut children = [0u32; 16];
        let mut any_live = false;

        for sign_col in 0u32..16 {
            let xv = (sign_col >> 0) & 1; // 0 = -1, 1 = +1
            let yv = (sign_col >> 1) & 1;
            let zv = (sign_col >> 2) & 1;
            let wv = (sign_col >> 3) & 1;

            // Symmetry breaking: at position 0, all must be +1
            if pos == 0 && sign_col != 0b1111 {
                continue;
            }

            let new_xb = xb | (xv << pos);
            let new_yb = yb | (yv << pos);
            let new_zb = zb | (zv << pos);
            let new_wb = wb | (wv << pos);

            // Check newly-completed lag constraints
            if !ctx.lags_complete_at_depth[d + 1].is_empty() {
                if !check_lags(new_xb, new_yb, new_zb, new_wb, &ctx.lags_complete_at_depth[d + 1], ctx) {
                    continue;
                }
            }

            let child = build(d + 1, new_xb, new_yb, new_zb, new_wb, ctx, nodes, dedup, leaf_count);
            if child != 0 {
                children[sign_col as usize] = child;
                any_live = true;
            }
        }

        if !any_live {
            return 0;
        }

        // Deduplicate
        if let Some(&existing) = dedup.get(&children) {
            return existing;
        }

        let nid = nodes.len() as u32;
        nodes.push(children);
        dedup.insert(children, nid);
        nid
    }

    let root = build(0, 0, 0, 0, 0, &ctx, &mut nodes, &mut dedup, &mut leaf_count);
    nodes[1] = nodes[root as usize]; // copy root into slot 1 if needed

    let node_count = nodes.len();
    let trie_bytes = node_count * 16 * 4; // 16 children × 4 bytes each
    eprintln!("\n--- Decision trie stats (k={}) ---", k);
    eprintln!("  Nodes: {}", node_count);
    eprintln!("  Leaves (valid 4-tuples): {}", leaf_count);
    eprintln!("  Trie size: {} bytes ({:.2} MB)", trie_bytes, trie_bytes as f64 / 1_048_576.0);
    eprintln!("  Current table size: 1923.1 MB (k=7)");
    eprintln!("  Compression ratio: {:.0}x", 1_923.1 * 1_048_576.0 / trie_bytes as f64);

    // Stats per depth
    eprintln!("\n  Depth breakdown:");
    // Count nodes reachable at each depth (BFS)
    let mut level_nodes: Vec<usize> = vec![0; 2 * k + 1];
    let mut current_level = vec![root];
    for d in 0..2 * k {
        level_nodes[d] = current_level.len();
        let mut next_level = std::collections::HashSet::new();
        for &nid in &current_level {
            if nid == 0 || nid == u32::MAX { continue; }
            for &child in &nodes[nid as usize] {
                if child != 0 {
                    next_level.insert(child);
                }
            }
        }
        current_level = next_level.into_iter().collect();
    }
    level_nodes[2 * k] = leaf_count as usize;
    for d in 0..=2 * k {
        let pos_str = if d < 2 * k { format!("pos {}", pos_order[d]) } else { "leaf".to_string() };
        eprintln!("    depth {:2} ({}): {} nodes", d, pos_str, level_nodes[d]);
    }
}
