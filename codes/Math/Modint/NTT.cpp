struct NTT {
  static_assert(maxn == (maxn & -maxn));
  Mint roots[maxn];
  NTT() {
    Mint r = Mint(G).qpow((mod - 1) / maxn);
    for (int i = maxn >> 1; i; i >>= 1) {
      roots[i] = 1;
      for (int j = 1; j < i; j++)
        roots[i + j] = roots[i + j - 1] * r;
      r = r * r;
      // for (int j = 0; j < i; j++) // FFT (tested)
      //   roots[i+j] = polar<llf>(1, PI * j / i);
    }
  }
  // n must be 2^k, and 0 <= f[i] < mod
  void operator()(Mint f[], int n, bool inv = false) {
    for (int i = 0, j = 0; i < n; i++) {
      if (i < j) swap(f[i], f[j]);
      for (int k = n>>1; (j^=k) < k; k>>=1);
    }
    for (int s = 1; s < n; s *= 2)
      for (int i = 0; i < n; i += s * 2)
        for (int j = 0; j < s; j++) {
          Mint a = f[i+j], b = f[i+j+s] * roots[s+j];
          f[i+j] = a + b; f[i+j+s] = a - b;
        }
    if (!inv) return;
    const Mint invn = Mint(n).inv();
    for (int i = 0; i < n; i++) f[i] *= invn;
    reverse(f + 1, f + n);
  }
};
