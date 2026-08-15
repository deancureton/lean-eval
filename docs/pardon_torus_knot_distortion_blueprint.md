# Pardon’s torus-knot distortion bound: proof and Lean blueprint

This note describes the proof of the `pardon_torus_knot_distortion` benchmark theorem and maps
each mathematical step to the solver modules under
`generated/pardon_torus_knot_distortion/Submission/`.  The formulation follows Pardon's
double-bubble proof, with rational boxes of aspect ratio `5/4` in place of irrational cube-root
boxes.  This change preserves the published constant `160` and makes all box arithmetic exact in
Lean.

## Statement and contradiction setup

Let `K : Knot` be smoothly ambient-isotopic, after a smooth increasing reparametrization, to the
standard `(p,q)` torus knot, with `p,q > 0` and coprime.  Write `D = distortion K`.  The target is

```text
(1/160) * min(p,q) ≤ D.
```

If `D = ∞`, the result is immediate.  Otherwise `D.toReal` is finite and it is enough to prove

```text
min(p,q) ≤ 160 * D.toReal.
```

Assume the strict opposite inequality.  We construct an infinite sequence of oriented boxes,
each containing the genus of the transported torus and each having scale at most `69/70` times
the preceding scale.  Compactness and local flatness say that sufficiently small portions of the
torus lie in a planar chart and cannot carry genus.  This contradicts the invariant maintained by
the nested sequence.

The extended-real reduction and the abstract nested-box contradiction are formalized in
`PardonReduction.lean`, `Shrinking.lean`, `LoopNested.lean`, `Topology/BasedLoopCarrier.lean`, and
`BasedPardonGeometricStep.lean`.

## 1. Metric estimate inside a box

For parameters `s,t`, the intrinsic distance along `K` is the shorter of the two arclengths between
them.  The distortion ratio is intrinsic distance divided by the Euclidean chord, and `distortion`
is the supremum of these ratios.

If two points of the knot lie in one oriented box of scale `r`, then the box diameter is less than
`5r`.  Therefore their Euclidean distance is less than `5r`, and the shorter knot arc between them
has length at most `5rD`.  The complementary arc has the same estimate when its endpoints are in
the box.  Cutting the parameter circle at the entry and exit points shows that the total arclength
of the portion of `K` lying in a closed box is at most `10rD`.

The elementary inequality needed here is not hidden in topology: it follows directly from the
definition of distortion as a supremum and the fundamental theorem of calculus estimate
`norm_sub_le_integral_of_norm_deriv_le_of_le`.  The corresponding Lean development is in
`ArcLength.lean`, `Distortion.lean`, `LocalArc.lean`, and the local integral lemmas used by the
boundary selectors.

## 2. Rational nested boxes

Use half-widths

```text
r, (5/4)r, (5/4)^2 r
```

in the three framed coordinate directions.  Their diameter is less than `5r`, because

```text
4 * (1 + (5/4)^2 + (5/4)^4) < 25.
```

After cutting perpendicular to the long axis, rotate the frame cyclically.  Half the old long
width fits in the new short width since `(5/4)^3 < 2`.  We first expand the box to a radius at most
`(8/7)r` and permit the cutting plane to move by at most `r/7` from the center.  Both resulting
half-boxes then fit in a cyclically oriented successor box of scale

```text
((1 + 1/7)/(5/4) + (1/7)/2)r = (69/70)r.
```

All of these are rational identities or strict rational inequalities.  They are proved in
`BoxGeometry.lean`, `OrientedBox.lean`, and the selection packaging modules.

## 3. The two coarea selections

First choose an outer scale `R` in `(r,(8/7)r]`.  Apply the one-dimensional coarea formula to the
Lipschitz rational-box gauge along the knot.  The local arclength bound is at most `10RD`, and the
available shell width is `r/7`.  A regular shell exists whose number of knot intersections is at
most

```text
80D.
```

The selected value simultaneously avoids all critical values of the six smooth face-coordinate
lifts of the transported torus.  Planar Sard–Moreira makes their union null, so the same shell is
regular on every face without changing the knot count.

Next choose a cutting height in the central interval of width `2r/7`.  Applying coarea to the long
coordinate gives at most

```text
40D
```

knot intersections.  The exceptional set is enlarged by the critical values of two smooth
independent carrier loops, and by the single long-coordinate value of their common basepoint.
These sets are null, so the count is unchanged.  Hence the cut is regular for the knot and both
loops, and the basepoint lies strictly on one side.

The branch-free Lipschitz coarea theorem, Sard port, and selectors are in `Coarea/General.lean`,
`Coarea/Lipschitz.lean`, `SardMoreira/`, `Coarea/FacewiseRegularOuterBoundarySelection.lean`,
`Coarea/SmoothCarrierPlaneSelection.lean`, and `Coarea/SmoothCarrierPlaneAvoiding.lean`.

## 4. Cutting the torus and the double-bubble alternative

The carried-genus witness consists of two loops on the transported torus with independent winding
pairs.  They pass through one common basepoint.  Smooth Fourier approximation preserves the
basepoint and both winding pairs while putting both loops in general position with the selected
plane.

The selected outer boundary and cutting disk form a double bubble.  Starting with the outer box
boundary, perform a one-parameter sphere surgery across the cutting disk.  At the end there are
the two half-box boundary spheres.  Put this family in general position with the transported
torus; away from finitely many surgery times, every intersection is a finite union of embedded
circles.

There are two cases.

1. Every intersection circle throughout the sphere surgery is inessential on the torus.  At a
   regular time, exactly one component of the torus cut along those circles retains the full
   rank-two image in `H₁(T²; ℚ)`; all other pieces are planar.  A single elementary surgery changes
   that image rank by at most one, while for a torus its possible full-genus values are zero and
   two.  Hence the full-genus component cannot disappear as the sphere varies.  At the terminal
   double bubble it lies inside one of the two half-boxes.  Choosing two based generators in that
   component gives the based independent winding-loop carrier needed for the shrinking step.

2. Some sphere in the family has an essential intersection circle.  Choose an innermost essential
   circle on that sphere.  The disk it bounds on the sphere contains only inessential torus
   intersections; repeatedly use an innermost-circle surgery to remove them.  The finite circle
   count strictly decreases, so the process terminates at an embedded disk whose boundary is
   essential on the torus and whose open interior misses the torus.  This is a genuine compressing
   disk.  The sphere-surgery trace shows that its boundary is assembled from outer-boundary arcs
   and two copies of cutting-disk arcs, which is exactly the later event charging.

The quotient-safe regular level and finite component framework is in
`Topology/CoordinatePlaneIntersectionCircles.lean`.  Regular planar charts descend through the
product-circle covering in `Topology/RegularLevelQuotientCharts.lean`; the compact connected
one-manifold classification is organized through the rotated-gradient flow in
`Topology/PeriodicOrbitClassification.lean` and `Topology/RegularLevelTangentODE.lean`.  The
explicit affine plane and containing disk are in `Topology/CoordinatePlane.lean` and
`Topology/CoordinatePlaneDisk.lean`.  Cyclic crossing bookkeeping and rerouting infrastructure is
in `Topology/SortedCrossingConstruction.lean`, `Topology/CrossingSignFlip.lean`,
`Topology/ArcReplacementConstruction.lean`, and the winding splice modules.  The finite surgery
termination proof is in `Topology/InnermostCircleSurgery.lean`.  The strong planar Schoenflies
source is vendored under `Submission/PlaneSchoenflies/`.  The remaining geometric integration is
the sphere-surgery family and its rank-two homology invariance; endpoint path connectivity alone
is intentionally not used as a substitute for that theorem.

## 5. Representativity of the transported `(p,q)` knot

Identify the transported torus with `Circle × Circle`.  A loop of winding `(m,n)` has algebraic
intersection with the `(p,q)` knot equal to

```text
p*n - q*m.
```

A compressing-disk boundary on the tube side has `m = 0`; on the exterior side it has `n = 0`.
Embeddedness and essentiality make the other coordinate primitive, hence its absolute value is
one.  Therefore the algebraic intersection has absolute value `p` or `q`, and the geometric
intersection count is at least `min(p,q)`.

The side classification is proved by explicit circle coordinates extending across the two
complementary solid tori; a nonzero winding coordinate cannot extend across a disk.  This avoids
assuming a general knot-complement classification theorem.  See `Topology/DiskWinding.lean`,
`Topology/SolidTorus.lean`, `Topology/GeneralCompression.lean`, and
`Topology/Representativity.lean`.

For the signed intersection certificate, a Bézout `SL(2,ℤ)` coordinate change sends the knot
slope `(p,q)` to `(1,0)`.  Intersections are exactly regular roots of the transformed second circle
coordinate.  The signed sum of those roots is its winding, namely `p*n-q*m`.  Half-open parameter
intervals count the seam once.  This direct one-dimensional construction is developed in
`Topology/CircleSignedDegree.lean`, `Topology/RegularCircleRootConstruction.lean`,
`Topology/RegularCircleRootDegree.lean`, `Topology/RegularCircleRootGlobalDegree.lean`, and
`Topology/SL2ZIntersectionCertificate.lean`.

## 6. Charging the compression and obtaining the contradiction

The compressing boundary is assembled from arcs in the outer box boundary and two copies of arcs
in the cutting plane.  Every intersection with the knot can therefore be charged injectively to
either one outer-boundary crossing or one of two tagged copies of a cutting-plane crossing.  The
number of available events is at most

```text
80D + 2 * 40D = 160D.
```

Representativity supplies at least `min(p,q)` distinct intersections.  Under the contrary
assumption `160D < min(p,q)`, no such injection can exist.  Consequently the compression branch
of the cut alternative is impossible, and one successor half-box must carry genus.  Iterating the
`69/70` shrink contradicts local flatness, proving the desired bound.

The event finsets, reparametrization transfer, injection, and final cardinal arithmetic are in
`DoubleBubbleSelection.lean`, `GeometricEventCharging.lean`, `ReparamCharging.lean`,
`CompressionExclusion.lean`, and `BasedPardonGeometricStep.lean`.

## Remaining kernel-level integration boundary

The numerical, coarea, compactness, winding, solid-torus, finite-surgery termination, and event
charging layers above are implemented and axiom-audited.  The last integration theorem must
assemble the regular plane-section circles, Schoenflies disks, excursion reroutings, and the
direct signed-root certificate into `HasBasedRegularResolvedDoubleBubbleSteps`, using the supplied
ambient-isotopy/reparametrization equation.  The benchmark capstone then consists only of choosing
that isotopy witness and invoking `pardonTarget_of_basedRegularResolvedDoubleBubbleSteps`.
