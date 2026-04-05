/// Measure the size of a 16-way decision trie for boundary configs.
///
/// Build approach: construct two 4-way tries (XY and ZW) from exhaustive
/// enumeration (67M configs each), then merge them into a 16-way trie
/// with lag-constraint pruning at each checkpoint.
///
/// The trie visits boundary positions in bouncing order: 0, 2k-1, 1, 2k-2, ...
/// After each pair of positions, one lag constraint becomes fully determined
/// and can prune dead branches during the merge.

use std::collections::HashMap;

const DEAD: u32 = 0;
const LEAF: u32 = 0xFFFF;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let k: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(7);

    eprintln!("Building decision trie for k={} (valid for all n >= {})", k, 2 * k);

    // Bouncing position order: 0, 2k-1, 1, 2k-2, 2, 2k-3, ...
    let mut pos_order: Vec<usize> = Vec::with_capacity(2 * k);
    for t in 0..k {
        pos_order.push(t);
        pos_order.push(2 * k - 1 - t);
    }
    eprintln!("Position order: {:?}", pos_order);

    // Build exact-lag bit pairs (same math as gen_table).
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

    // Which lags become fully determined after placing positions 0..depth-1?
    let mut lags_complete_at_depth: Vec<Vec<usize>> = vec![Vec::new(); 2 * k + 1];
    for (lag_idx, lag) in exact_lags.iter().enumerate() {
        let mut all_positions = std::collections::HashSet::new();
        for &(a, b) in &lag.xy_pairs { all_positions.insert(a); all_positions.insert(b); }
        for &(a, b) in &lag.w_pairs { all_positions.insert(a); all_positions.insert(b); }
        let max_depth = all_positions.iter()
            .map(|&pos| pos_order.iter().position(|&p| p == pos).unwrap())
            .max().unwrap_or(0);
        lags_complete_at_depth[max_depth + 1].push(lag_idx);
    }

    for d in 0..=2 * k {
        if !lags_complete_at_depth[d].is_empty() {
            eprintln!("  After depth {}: lags {:?} fully determined", d, lags_complete_at_depth[d]);
        }
    }

    // ========== Phase 1: Build 4-way XY trie ==========
    eprintln!("\nPhase 1: Building 4-way XY trie...");
    let xy_trie = build_4way_trie(k, &pos_order, true);
    eprintln!("  XY trie: {} nodes", xy_trie.nodes.len());

    // ========== Phase 2: Build 4-way ZW trie ==========
    eprintln!("Phase 2: Building 4-way ZW trie...");
    let zw_trie = build_4way_trie(k, &pos_order, false);
    eprintln!("  ZW trie: {} nodes", zw_trie.nodes.len());

    // ========== Phase 3: Merge into 16-way trie ==========
    eprintln!("Phase 3: Merging with lag-constraint pruning...");

    let mut merged_nodes: Vec<[u32; 16]> = Vec::new();
    merged_nodes.push([0u32; 16]); // node 0 = DEAD sentinel

    let mut merge_dedup: HashMap<[u32; 16], u32> = HashMap::new();
    merge_dedup.insert([0u32; 16], DEAD);

    // Memoize on (xy_node, zw_node) → merged_node_id
    let mut merge_memo: HashMap<(u32, u32), u32> = HashMap::new();
    let mut leaf_count: u64 = 0;

    fn merge(
        d: usize,
        xy_nid: u32, zw_nid: u32,
        // Partial bit patterns for lag checking at constraint checkpoints
        xb: u32, yb: u32, zb: u32, wb: u32,
        pos_order: &[usize],
        exact_lags: &[ExactLag],
        lags_complete: &[Vec<usize>],
        xy_trie: &Trie4,
        zw_trie: &Trie4,
        merged_nodes: &mut Vec<[u32; 16]>,
        merge_dedup: &mut HashMap<[u32; 16], u32>,
        merge_memo: &mut HashMap<(u32, u32), u32>,
        leaf_count: &mut u64,
    ) -> u32 {
        // Check memo
        let memo_key = (xy_nid, zw_nid);
        if let Some(&cached) = merge_memo.get(&memo_key) {
            // Count leaves for cached subtrees too? No — we only count on first visit.
            return cached;
        }

        let depth = pos_order.len();

        // Both at leaf = valid 4-tuple
        if d == depth {
            if xy_nid == LEAF && zw_nid == LEAF {
                *leaf_count += 1;
                let result = LEAF;
                merge_memo.insert(memo_key, result);
                return result;
            } else {
                merge_memo.insert(memo_key, DEAD);
                return DEAD;
            }
        }

        // If either trie is dead, merged is dead
        if xy_nid == DEAD || zw_nid == DEAD {
            merge_memo.insert(memo_key, DEAD);
            return DEAD;
        }

        let pos = pos_order[d];
        let xy_children = &xy_trie.nodes[xy_nid as usize];
        let zw_children = &zw_trie.nodes[zw_nid as usize];
        let mut children = [0u32; 16];
        let mut any_live = false;

        for xy_branch in 0u32..4 {
            let xy_child = xy_children[xy_branch as usize];
            if xy_child == DEAD { continue; }

            let xv = (xy_branch >> 0) & 1;
            let yv = (xy_branch >> 1) & 1;

            for zw_branch in 0u32..4 {
                let zw_child = zw_children[zw_branch as usize];
                if zw_child == DEAD { continue; }

                let zv = (zw_branch >> 0) & 1;
                let wv = (zw_branch >> 1) & 1;

                let new_xb = xb | (xv << pos);
                let new_yb = yb | (yv << pos);
                let new_zb = zb | (zv << pos);
                let new_wb = wb | (wv << pos);

                // Check newly-completed lag constraints
                if !lags_complete[d + 1].is_empty() {
                    let mut ok = true;
                    for &li in &lags_complete[d + 1] {
                        let nx = bnd_autocorr(new_xb, &exact_lags[li].xy_pairs);
                        let ny = bnd_autocorr(new_yb, &exact_lags[li].xy_pairs);
                        let nz = bnd_autocorr(new_zb, &exact_lags[li].z_pairs);
                        let nw = bnd_autocorr(new_wb, &exact_lags[li].w_pairs);
                        if nx + ny + 2 * nz + 2 * nw != 0 {
                            ok = false;
                            break;
                        }
                    }
                    if !ok { continue; }
                }

                let sign_col = xv | (yv << 1) | (zv << 2) | (wv << 3);
                let child = merge(
                    d + 1, xy_child, zw_child,
                    new_xb, new_yb, new_zb, new_wb,
                    pos_order, exact_lags, lags_complete,
                    xy_trie, zw_trie,
                    merged_nodes, merge_dedup, merge_memo, leaf_count,
                );
                if child != DEAD {
                    children[sign_col as usize] = child;
                    any_live = true;
                }
            }
        }

        if !any_live {
            merge_memo.insert(memo_key, DEAD);
            return DEAD;
        }

        // Deduplicate merged node
        let nid = if let Some(&existing) = merge_dedup.get(&children) {
            existing
        } else {
            let nid = merged_nodes.len() as u32;
            merged_nodes.push(children);
            merge_dedup.insert(children, nid);
            nid
        };
        merge_memo.insert(memo_key, nid);
        nid
    }

    let root = merge(
        0, xy_trie.root, zw_trie.root,
        0, 0, 0, 0,
        &pos_order, &exact_lags, &lags_complete_at_depth,
        &xy_trie, &zw_trie,
        &mut merged_nodes, &mut merge_dedup, &mut merge_memo, &mut leaf_count,
    );

    let node_count = merged_nodes.len();
    let trie_bytes = node_count * 16 * 4;
    eprintln!("\n--- Decision trie stats (k={}) ---", k);
    eprintln!("  XY trie nodes: {}", xy_trie.nodes.len());
    eprintln!("  ZW trie nodes: {}", zw_trie.nodes.len());
    eprintln!("  Merge memo entries: {}", merge_memo.len());
    eprintln!("  Merged 16-way nodes: {}", node_count);
    eprintln!("  Leaves (valid 4-tuples): {} (undercounted — only first visit)", leaf_count);
    eprintln!("  Trie size: {} bytes ({:.2} MB)", trie_bytes, trie_bytes as f64 / 1_048_576.0);
    eprintln!("  Current table size: 1923.1 MB (k=7)");
    if trie_bytes > 0 {
        eprintln!("  Compression ratio: {:.0}x", 1_923.1 * 1_048_576.0 / trie_bytes as f64);
    }

    // BFS depth breakdown
    eprintln!("\n  Depth breakdown (merged):");
    let mut current_level: Vec<u32> = vec![root];
    for d in 0..2 * k {
        let pos_str = format!("pos {}", pos_order[d]);
        eprintln!("    depth {:2} ({}): {} unique nodes", d, pos_str, current_level.len());
        let mut next_level = std::collections::HashSet::new();
        for &nid in &current_level {
            if nid == DEAD || nid == LEAF { continue; }
            for &child in &merged_nodes[nid as usize] {
                if child != DEAD {
                    next_level.insert(child);
                }
            }
        }
        current_level = next_level.into_iter().collect();
    }
    eprintln!("    depth {:2} (leaf): {} unique nodes", 2 * k, current_level.len());
}

/// A 4-way trie: at each level, branch on 2 bits (either x,y or z,w at the current position).
struct Trie4 {
    nodes: Vec<[u32; 4]>, // nodes[0] = DEAD, nodes[root] = root
    root: u32,
}

fn build_4way_trie(k: usize, pos_order: &[usize], is_xy: bool) -> Trie4 {
    let depth = 2 * k;
    // Symmetry breaking: a[0]=b[0]=+1
    // For XY: x[0]=y[0]=+1, enumerate 2*(2k-1) free bits
    // For ZW: z[0]=w[0]=+1, enumerate 2*(2k-1) free bits
    let free_per_seq = 2 * k - 1; // positions 1..2k-1
    let total_configs = 1u64 << (2 * free_per_seq); // 2 sequences × free_per_seq bits

    let mut nodes: Vec<[u32; 4]> = Vec::new();
    nodes.push([DEAD; 4]); // node 0 = DEAD sentinel

    let mut dedup: HashMap<[u32; 4], u32> = HashMap::new();
    dedup.insert([DEAD; 4], DEAD);

    // Build by inserting each config into the trie
    let mut root = DEAD;
    let mut count = 0u64;

    for bits in 0..total_configs {
        // Decode: seq_a[0]=seq_b[0]=+1, free bits for positions 1..2k-1
        let mut ab = 1u32; // a[0]=+1
        let mut bb = 1u32; // b[0]=+1
        let mut bi = 0usize;
        for i in 1..(2 * k) {
            let v = ((bits >> bi) & 1) as u32;
            bi += 1;
            ab |= v << i;
        }
        for i in 1..(2 * k) {
            let v = ((bits >> bi) & 1) as u32;
            bi += 1;
            bb |= v << i;
        }

        // Insert into trie following pos_order
        root = insert_4way(
            root, ab, bb, 0, pos_order, depth,
            &mut nodes, &mut dedup,
        );
        count += 1;
        if count % 10_000_000 == 0 {
            eprintln!("  inserted {}M / {}M configs, {} nodes",
                count / 1_000_000, total_configs / 1_000_000, nodes.len());
        }
    }

    eprintln!("  {} configs inserted, {} unique nodes", count, nodes.len());
    Trie4 { nodes, root }
}

fn insert_4way(
    nid: u32,
    ab: u32, bb: u32,
    d: usize,
    pos_order: &[usize],
    depth: usize,
    nodes: &mut Vec<[u32; 4]>,
    dedup: &mut HashMap<[u32; 4], u32>,
) -> u32 {
    if d == depth {
        return LEAF;
    }

    let pos = pos_order[d];
    let av = (ab >> pos) & 1;
    let bv = (bb >> pos) & 1;
    let branch = (av | (bv << 1)) as usize;

    // Get or create node
    let node_id = if nid == DEAD {
        let id = nodes.len() as u32;
        nodes.push([DEAD; 4]);
        id
    } else {
        nid
    };

    let old_child = nodes[node_id as usize][branch];
    let new_child = insert_4way(old_child, ab, bb, d + 1, pos_order, depth, nodes, dedup);
    nodes[node_id as usize][branch] = new_child;

    node_id
}

fn bnd_autocorr(bits: u32, pairs: &[(usize, usize)]) -> i32 {
    let mut val = 0i32;
    for &(bi, bj) in pairs {
        val += 1 - 2 * (((bits >> bi) ^ (bits >> bj)) & 1) as i32;
    }
    val
}
