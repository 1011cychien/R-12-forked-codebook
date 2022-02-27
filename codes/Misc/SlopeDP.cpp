struct L {
  mutable int64_t a, b, p;
  bool operator<(const L &r) const { return a < r.a; }
  bool operator<(int64_t x) const { return p < x; }
};
struct DynamicHull : multiset<L, less<>> {
  static const int64_t kInf = 1e18;
  bool Isect(iterator x, iterator y) {
    auto Div = [](int64_t a, int64_t b) {
        return a / b - ((a ^ b) < 0 && a % b); }
    if (y == end()) { x->p = kInf; return false; }
    if (x->a == y->a) x->p = x->b > y->b ? kInf : -kInf;
    else x->p = Div(y->b - x->b, x->a - y->a);
    return x->p >= y->p;
  }
  void Insert(int64_t a, int64_t b) {
    auto z = insert({a, b, 0}), y = z++, x = y;
    while (Isect(y, z)) z = erase(z);
    if (x!=begin()&&Isect(--x,y)) Isect(x, y=erase(y));
    while ((y = x) != begin() && (--x)->p >= y->p)
      Isect(x, erase(y));
  }
  int64_t Query(int64_t x) {
    auto l = *lower_bound(x);
    return l.a * x + l.b;
  }
};
