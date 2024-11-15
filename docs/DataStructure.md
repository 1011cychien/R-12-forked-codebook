# Data Structure

## Dark Magic
### Description
PBDS classes/functions.
ordered set and mergeable heap are the useful ones.
### Test Status
No test.

## Link-Cut Tree
### Description
$O(Q\log N)$ operations on path query.
Supports link or cut edge.

Subtree queries are tricky.
### Test Status
[CF 603E](https://codeforces.com/contest/603/submission/248352970).
Passed [dynamic_tree_vertex_set_path_composite](https://judge.yosupo.jp/submission/193553) and [dynamic_tree_vertex_add_subtree_sum](https://judge.yosupo.jp/submission/193554).

## LiChao Segtree
### Description
Maintain the upper envelope of lines.

TODO: is extended version needed?
### Test Status
Used in some contest.
Passed [Line Add Get Min](https://judge.yosupo.jp/submission/194542)

## Treap
### Description
treap. For persistent, should not use `pri`.
### Test Status
Rarely used. Need test?

## Linear Basis
### Description
Given a set of integers:
- `query_kth` to find the $k$-th integer in the (sorted)
    set of XOR combination of the integers with $v$.
- The `second` field is for range XOR basis query or smt,
    greedily maintained in `insert` function.

### Test Status
- [ABC223 H](https://atcoder.jp/contests/abc223/submissions/35070056)
- kth problem [1st Hunger Games S](https://codeforces.com/group/qcIqFPYhVr/contest/203881/problem/S)
- maybe need a combined problem?

## <atcoder/lazysegtree>
### Description
Iterative segment tree with lazy tag.
### Test status
Passed [range_affine_range_sum](https://judge.yosupo.jp/submission/247177).

## Binary Search on Segtree
### Description
Binary search on ZKW segtree.
`sz` should be power of $2$ (be careful of other parts!).
### Test Status
Passed [Quick Sort](https://codeforces.com/gym/104076/problem/G)

## Interval Container
### Description
Maintains intervals. Copied from KACTL.
### Test Status
No.
