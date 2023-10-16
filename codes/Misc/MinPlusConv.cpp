vector<int> min_plus_convolution(auto &a, auto &b) {
  const int n = (int)a.size(), m = (int)b.size();
  vector<int> c(n + m - 1, numeric_limits<int>::max());
  auto dc = [&](auto Y, int l, int r, int jl, int jr) {
    if (l > r) return;
    int mid = (l + r) / 2, from = -1, &best = c[mid];
    for (int j = jl; j <= jr; j++)
      if (int i = mid - j; i >= 0 && i < n)
        if (best > a[i] + b[j]) best = a[i] + b[j], from = j;
    Y(Y, l, mid-1, jl, from); Y(Y, mid+1, r, from, jr);
  };
  return dc(dc, 0, n-1+m-1, 0, m-1), c;
}
