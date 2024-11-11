/* or convolution:
 * x = (x0, x0+x1), inv = (x0, x1-x0) w/o final div
 * and convolution:
 * x = (x0+x1, x1), inv = (x0-x1, x1) w/o final div */
template <typename T>
void fwt(T x[], int N, bool inv = false) {
  for (int d = 1; d < N; d <<= 1)
    for (int s = 0; s < N; s += d * 2)
      for (int i = s; i < s + d; i++) {
        int j = i + d;
        T ta = x[i], tb = x[j];
        x[i] = ta + tb; x[j] = ta - tb;
      }
  if (!inv) return;
  const T invn = T(N).inv();
  for (int i = 0; i < N; i++) x[i] *= invn;
}
