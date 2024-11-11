template <typename S, auto op, auto e,
  typename F, auto mapping, auto composition, auto id>
struct lazy_segtree {
  int n, sz, lg; vector<S> d; vector<F> lz;
  void upd(int i, F f) {
    d[i] = mapping(f, d[i]);
    if (i < sz) lz[i] = composition(f, lz[i]);
  }
  void pull(int p) {
    while (p >>= 1) {
      d[p] = op(d[p << 1], d[p << 1 | 1]);
      d[p] = mapping(lz[p], d[p]);
    }
  }
  void push(int p) {
    for (int h = lg; h >= 0; h--)
      if (int i = p >> h; i > 1) {
        upd(i, lz[i >> 1]);
        upd(i ^ 1, lz[i >> 1]);
        lz[i >> 1] = id();
      }
  }
  void set(int p, S v) {
    assert(0 <= p && p < n);
    p += sz, push(p), d[p] = v, pull(p);
  }
  S get(int p) {
    assert(0 <= p && p < n);
    return p += sz, push(p), d[p];
  }
  void apply(int l, int r, F f) {
    assert(0 <= l && l < r && r <= n);
    int tl = l, tr = r;
    push(l + sz), push(r - 1 + sz);
    for (l += sz, r += sz; l < r; l >>= 1, r >>= 1) {
      if (l & 1) upd(l++, f);
      if (r & 1) upd(--r, f);
    }
    pull(tl + sz), pull(tr - 1 + sz);
  }
  S prod(int l, int r) {
    assert(0 <= l && l < r && r <= n);
    push(l + sz), push(r - 1 + sz);
    S resl = e(), resr = e();
    for (l += sz, r += sz; l < r; l >>= 1, r >>= 1) {
      if (l & 1) resl = op(resl, d[l++]);
      if (r & 1) resr = op(d[--r], resr);
    }
    return op(resl, resr);
  }
  S all_prod() const { return d[1]; }
  lazy_segtree(const vector<S> &v) : n((int)v.size()),
    sz((int)bit_ceil(v.size())), lg(__lg(sz)),
    d(sz * 2, e()), lz(sz, id()) {
      for (int i = 0; i < n; i++)
        d[i + sz] = v[i];
      for (int i = sz - 1; i > 0; i--)
        d[i] = op(d[i << 1], d[i << 1 | 1]);
    }
};
// https://judge.yosupo.jp/submission/247007
// https://judge.yosupo.jp/submission/247009
