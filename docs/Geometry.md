# Geometry

## Basic Geometry

### Description
- `sgn` `cross` `dot` `ori`
- `quad` `argCmp` all-integer angle compare.
- `area` be careful of type.
- `rot90` multiply by $i$ (or left turn 90 degree)
- `project` projection onto a vector

Be careful that PF can be implicitly cast to PT.
### Test Status
No test. Used extensively in other template.
[argCmp](https://judge.yosupo.jp/submission/201631)
[center of polygon](https://codeforces.com/gym/104945/submission/255847017)

## 2D Convex Hull

### Description
Returns strict convex hull of given points.
The result is counter-clockwise and the first point is the lex-min point.
Be careful about edge case (0/1/2/3 points on CV)
### Test Status
Used in some contest.
Passed codeforces [87 E](https://codeforces.com/contest/87/submission/248359853).

## 2D Farthest Pair
### Description
Rotating caliper algorithm.
Requires the input hull be strictly convex.
### Test Status
Passed AOJ CGL.

## MinMax Enclosing Rect
### Description
Rotating caliper, but with more pointers.
### Test Status
Passed UVA 819

## Minkowski Sum
### Description
Minkowski sum of two convex hulls.
### Test Status
Used in some contest. TODO.
Passed codeforces [87 E](https://codeforces.com/contest/87/submission/248359853).
Passed [~~non-flying weather~~](https://acm.timus.ru/problem.aspx?space=1&num=1894).

## Segment Intersection
### Description
Check whether the segment intersects. Touching at the ends counts.
Be careful about edge case like parallel, does touching at ends count, ...
Can be modified to `Ray` class or `Line` class.

To get the intersection point, check next part (HPI)

### Test Status
Used in many contest. Passed [AOJ CGL](https://judge.u-aizu.ac.jp/onlinejudge/review.jsp?rid=9068290#1).

## Halfplane Intersection
### Description
Calculate the area of half-plane-intersection.
The result lines will be in `q` (this is why we need the reference).
Result lines maybe wrong if the intersection area doesn't have positive area.
### Test Status
Passed 2020 Nordic NCPC [Big brother](https://ncpc20.kattis.com/submissions/12966548).
Passed 2023 NTU preliminary [Area in Convex](https://codeforces.com/gym/104508/submission/249736618)

Used in many contest.

Passed POJ 3384, 3525.

## HPI Alternative Form
### Description
$ax + by + c \le 0$ form HPI.

### Tetst Status
Passed 2020 Nordic NCPC [Big brother](https://ncpc20.kattis.com/submissions/13150789).
Passed 2023 NTU preliminary [Area in Convex](https://codeforces.com/gym/104508/submission/249739247)

## SegmentDist (Sausage)
### Description
Distance from point to segment and segment to segment.
Can be used in checking sausage intersection.
### Test Status
Passed QOJ 2444 and PTZ 19 summer D3.

## Rotating Sweep Line
### Description
A skeleton of rotating sweep line.
Support colinear cases.
### Test Status
Passed [NAIPC 2016 G](https://codeforces.com/gym/101002/submission/228911692)

## Hull Cut
### Description
Cut convex polygon by a line.
Copied from kactl.

### Test Status
[AOJ](https://judge.u-aizu.ac.jp/onlinejudge/review.jsp?rid=9075877#1).

## Point In Hull
### Description
Testing PIH in $O(\log N)$.
### Test Status
[Enclosure](https://codeforces.com/gym/101201/submission/248361130)
See tangent of points to hull
Used in some contest.

## Point In Polygon
### Description
Testing PIP.
### Test Status
Used in some contest.
Passed [CGL_3_C](https://judge.u-aizu.ac.jp/onlinejudge/review.jsp?rid=8894196#1)

## Point In Polygon (Fast)
### Description
Testing PIP offline and faster.
### Test Status
Passed [CGL_3_C](https://judge.u-aizu.ac.jp/onlinejudge/review.jsp?rid=8894195#1)

## Cyclic Ternary Search
### Description
Fine extreme point on cyclic good functions
### Test Status
See tangent of points to hull

## Tangent of Points to Hull
### Description
Tangent of point to hull in $O(\log N)$.
Requires the hull to be strictly convex.
Can be modified to find extreme point on hull.

### Test Status
[Enclosure](https://codeforces.com/gym/101201/submission/248361130)

## Circle Class & Intersection
### Description
Definition of `Cir` and some intersection function.
### Test Status
Passed AOJ CGL.
[CGL_7_E](https://judge.u-aizu.ac.jp/onlinejudge/review.jsp?rid=8894166#1)

## Circle Common Tangent
### Description
Common tangent point of circle.
### Test Status
Passed AOJ [CGL_7_F](https://judge.u-aizu.ac.jp/onlinejudge/review.jsp?rid=8894179#1), [CGL_7_G](https://judge.u-aizu.ac.jp/onlinejudge/review.jsp?rid=8894172#1).
Passed [CF 128E](https://codeforces.com/contest/128/submission/246025990).

## Line-Circle Intersection
### Description
The point of intersection of line and circle.
### Test Status
Passed AOJ [CGL_7_D](https://judge.u-aizu.ac.jp/onlinejudge/review.jsp?rid=8894183#1).

## Poly-Circle Intersection
### Description
The intersection area of a circle and a simple polygon.
### Test Status
Passed AOJ [CGL_7_H](https://judge.u-aizu.ac.jp/onlinejudge/review.jsp?rid=8894161#1).
Copied from 8BQube and they say it passed HDU2892.

## Min Covering Circle
### Description
Get minimum covering circle in $O(N)$ expected time.
Also gives the circumcenter formula.
### Test Status
Passed TIOJ 1093, luogu P1742
[~~TIOJ~~](https://tioj.ck.tp.edu.tw/submissions/370344)
[luogu](https://www.luogu.com.cn/record/148473379)

## Circle Union
### Description
Calculate the area that covered by at least $k$ circle for each $k$.
Time complexity $O(N^2\log N)$.
### Test Status
Passed SPOJ.
[CIRU](https://www.spoj.com/status/ns=32615293) (need 2d array instead of vector).
[CIRUT](https://www.spoj.com/status/ns=32615293)

## Polygon Union
### Description
Union area of simple polygon.
### Test Status
https://codeforces.com/gym/101673/submission/244046248

## 3D Point
### Description
Basic 3d point.
- cross
- triple product
- rotate around an axis
### Test Status
`rotate_around` is copied from NaCl.
Others are tested by 3d hull.

## 3D Convex Hull
### Description
Return the face of 3d convex hull of $N$ points.
There will be $O(N)$ faces and time complexity is $O(N^2)$.
Be careful of degenerate cases.
### Test Status
Passed SPOJ and [stars in a can](https://open.kattis.com/problems/starsinacan).
Passed [HDU 3662](https://vjudge.net/solution/46392862). (need to combine coplanar triangles to one face).

## 3D Projection
### Description
Get the 2d coordinate of the projection
of a point $p$ onto plane $q^Tx = 0$.
### Test Status
Passed [stars in a can](https://open.kattis.com/problems/starsinacan).

## Delaunay
### Description
Delaunay triangulation.

Usage TODO.

### Test Status
Passed [Brazil subregional](https://codeforces.com/gym/104555/submission/248361950).

## Build Voronoi
### Description
Voronoi diagram building.
### Test Status
Passed [Brazil subregional](https://codeforces.com/gym/104555/submission/248361950).

## kd Tree (Nearest Point)
### Description
KD Tree nearest point query.
### Test Status
TODO

## kd Closest Pair (3D ver.)
### Description
3d closest pair
### Test Status
Correct, but might be too slow. Can pass [TIOJ](https://tioj.ck.tp.edu.tw/submissions/357857) using fast hash table.  
Need more test.

## Simulated Annealing
### Description
A skeleton of simulated annealing
### Test Status
TODO.

## Triangle Centers 
### Description
Triangle centers formula.
### Test Status
No test.
