#define fi(l, r) for (size_t i = (l); i < (r); i++)
struct S : vector<Mint> {
  using V = vector<Mint>; using V::V;
  friend S operator*(S a, S b) { // (*@\Mul@*)
    if (a.empty() || b.empty()) return S();
    const auto k = a.size() + b.size() - 1;
    const int sz = (int)bit_ceil(k);
    a.resize(sz), b.resize(sz);
    ntt(a.data(), sz); ntt(b.data(), sz);
    fi(0, a.size()) a[i] *= b[i];
    return ntt(a.data(), sz, true), a.resize(k), a;
  } // (*@\MulEnd@*)
  S newton(Mint init, auto &&iter) const { // (*@\Newton@*)
    S Q = { init };
    for (int sz = 2; Q.size() < size(); sz *= 2) {
      S A(begin(), begin() + min(sz, int(size())));
      iter(Q, A, sz); Q.resize(sz);
    }
    return Q.resize(size()), Q;
  } // (*@\NewtonEnd@*)
  S inv() const { // (*@\Inv@*); coef[0] != 0
    return newton(front().inv(), [](S &X, S &A, int sz) {
      sz *= 2; X.resize(sz), A.resize(sz);
      ntt(X.data(), sz), ntt(A.data(), sz);
      for (int i = 0; i < sz; i++) X[i] *= 2 - X[i]*A[i];
      ntt(X.data(), sz, true); });
  } // (*@\InvEnd@*)
  S derivative() const { // (*@\Derivative@*)
    S A = *this;
    fi(1, A.size()) A[i - 1] = i * A[i];
    return A.empty() ? A : (A.pop_back(), A);
  } // (*@\DerivativeEnd@*)
  S integral() const { // (*@\Integral@*)
    S A = *this; A.insert(A.begin(), 0);
    fi(1, A.size()) A[i] /= i;
    return A;
  } // (*@\IntegralEnd@*)
  S log() const { // (*@\Log@*); coef[0] == 1; res[0] == 0
    auto B = (derivative() * inv()).integral();
    return B.resize(size()), B;
  } // (*@\LogEnd@*)
  S exp() const { // (*@\Exp@*); coef[0] == 0; res[0] == 1
    return newton(1, [](S &X, S &A, int sz) {
      X.resize(sz); A.resize(sz); S Y = X.log();
      fi(0, Y.size()) Y[i] = A[i] - Y[i];
      Y[0] += 1; X = X * Y; });
  } // (*@\ExpEnd@*)
  S mulT(S b, size_t k) const { // (*@\MulT@*)
    assert(b.size()); reverse(b.begin(), b.end());
    auto R = (*this) * b;
    R = S(R.begin() + b.size() - 1, R.end());
    return R.resize(k), R;
  } // (*@\MulTEnd@*)
  V evaluate(const V &x) { // (*@\Eval@*)
    if (empty()) return V(x.size());
    const int n = int(max(x.size(), size()));
    vector<S> q(n * 2, S{1}); V ans(n);
    fi(0, x.size()) q[i + n] = S{1, -x[i]};
    for (int i = n - 1; i > 0; i--)
      q[i] = q[i << 1] * q[i << 1 | 1];
    q[1] = mulT(q[1].inv(), n);
    for (int i = 1; i < n; i++) {
      auto L = q[i << 1], R = q[i << 1 | 1];
      q[i << 1 | 0] = q[i].mulT(R, L.size());
      q[i << 1 | 1] = q[i].mulT(L, R.size());
    }
    for (int i = 0; i < n; i++) ans[i] = q[i + n][0];
    return ans.resize(x.size()), ans;
  } // (*@\EvalEnd@*)
  friend S operator*(S a, Mint s) {
    for (Mint &x : a) x *= s;
    return a;
  }
};
S pow(S a, lld M) { // (*@\Pow@*); period mod*(mod-1)
  assert(!a.empty() && a[0] != 0);
  Mint c = a[0]; a = (a * c.inv()).log() * (M % mod);
  return a.exp() * c.qpow(M % (mod - 1));
} // (*@\PowEnd@*) mod x^N where N=a.size()
S sqrt(S v) { // (*@\Sqrt@*); need: QuadraticResidue
  assert(!v.empty() && v[0] != 0);
  const int r = get_root((int)v[0]); assert(r != -1);
  return v.newton(r,
      [inv2 = (mod + 1) / 2](S &X, S &A, int sz) {
        X.resize(sz); A.resize(sz);
        auto B = A * X.inv();
        for (int i = 0; i < sz; i++)
          X[i] = (X[i] + B[i]) * inv2; });
} // (*@\SqrtEnd@*)
pair<S, S> divmod(const S &A, const S &B) { // (*@\Div@*)
  assert(!B.empty() && B.back() != 0);
  if (A.size() < B.size()) return {{}, A};
  const auto sz = A.size() - B.size() + 1;
  S X = B; reverse(all(X)); X.resize(sz);
  S Y = A; reverse(all(Y)); Y.resize(sz);
  S Q = X.inv() * Y; Q.resize(sz); reverse(all(Q));
  X = Q * B; Y = A;
  fi(0, Y.size()) Y[i] -= X[i];
  while (Y.size() && Y.back() == 0) Y.pop_back();
  while (Q.size() && Q.back() == 0) Q.pop_back();
  return {Q, Y};
} // (*@\DivEnd@*) empty means zero polynomial
Mint linear_recursion_kth(S a, S c, int64_t k) { // (*@\LinearRec@*)
  const auto d = a.size(); assert(c.size() == d + 1);
  const int sz = (int)bit_ceil(2 * d + 1), o = sz / 2;
  S q = c; for (Mint &x: q) x = -x; q[0] = 1;
  S p = a * q; p.resize(sz); q.resize(sz);
  for (int r; r = (k & 1), k; k >>= 1) {
    fill(d + all(p), 0); fill(d + 1 + all(q), 0);
    ntt(p.data(), sz); ntt(q.data(), sz);
    for (int i = 0; i < sz; i++)
      p[i] *= q[(i + o) & (sz - 1)];
    for (int i = 0, j = o; j < sz; i++, j++)
      q[i] = q[j] = q[i] * q[j];
    ntt(p.data(), sz, true); ntt(q.data(), sz, true);
    for (size_t i = 0; i < d; i++) p[i] = p[i << 1 | r];
    for (size_t i = 0; i <= d; i++) q[i] = q[i << 1];
  } // Bostan-Mori
  return p[0] / q[0];
} // (*@\LinearRecEnd@*) a_n = \sum c_j a_(n-j), c_0 is not used
