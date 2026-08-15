# Pardon’s torus-knot distortion bound: proof and Lean blueprint

This note describes the proof of the `pardon_torus_knot_distortion` benchmark theorem and maps
each mathematical step to the solver modules under
`generated/pardon_torus_knot_distortion/Submission/`.  The formulation follows Pardon's
double-bubble proof.  Rational boxes of aspect ratio `5/4` control the nesting, while a smooth
degree-256 superellipsoid is used for the actual outer cut.  The smooth body removes all
face/ridge compatibility issues, preserves the exact shrink factor, and improves the event bound
from the published `160D` to `156D`.

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

## 3. The two smooth coarea selections

In framed, normalized coordinates put

```text
G(x) = (Σᵢ |xᵢ|^256)^(1/256),       P(x) = Σᵢ xᵢ^256.
```

Thus `G ≤ R` and `P ≤ R^256` describe the same closed superellipsoid.  Write

```text
a = 193/192,       b = 8/7.
```

The rational box of scale `r` is contained in the superellipsoid of scale `a r`, while the
superellipsoid of scale `R` is contained in the rational box of scale `R`.  The latter box has the
sharper diameter bound `(9/2)R`.  Hence the portion of the knot in the body has arclength at most
`9RD`.  The gauge is `a`-Lipschitz in the ambient Euclidean metric.  Applying the branch-free
one-dimensional coarea theorem over the interval `(a r,b r]` therefore gives a scale `R` with

```text
#(K ∩ {G = R}) ≤ a * 9b/(b-a) * D < 76D.
```

The same `R` is chosen so that `R^256` is a regular value of `P` restricted to the transported
torus.  Planar Sard says that the polynomial critical values form a null set.  On the compact
positive scale interval, the positive 256th-root map is Lipschitz, so pulling those values back to
scales preserves nullity.  Thus regularity costs no intersections.

Next choose a cutting height in the central interval of width `2r/7`.  Applying coarea to the long
coordinate gives at most

```text
40D
```

knot intersections.  The exceptional set is enlarged by three further null sets: the critical
values of the long coordinate on the whole transported torus, the critical heights of the
one-dimensional outer seam, and the finitely many heights of knot points already counted on the
outer surface.  The first set is null by planar Sard.  For the second, apply equal-dimensional
Sard to the planar map `(P,height) : ℝ² → ℝ²`.  A determinant-critical seam point maps
to a critical value of this pair.  The critical-value set is planar-null, so Fubini says that its
vertical section is one-dimensional-null for almost every polynomial level.  The outer scale is
chosen to avoid the exceptional levels, using the same locally Lipschitz positive 256th-root map
as above.  Avoiding the third finite set makes the outer and cutting event sets literally
disjoint.

The branch-free Lipschitz coarea theorem, Sard port, and smooth selectors are in
`Coarea/General.lean`, `Coarea/Lipschitz.lean`, `SardMoreira/`,
`SuperellipsoidGeometry.lean`, `Coarea/SuperellipsoidOuterSelection.lean`,
`Coarea/SuperellipsoidCriticalScales.lean`, `Coarea/SuperellipsoidCutSelection.lean`, and the
Sard–Fubini seam selector.

## 4. Cutting the torus and the double-bubble alternative

The outer superellipsoid and the cutting disk form a double bubble.  Perform the standard
two-surgery on the outer sphere along the disk.  This gives a one-parameter family of embedded
spheres; at the terminal time it is the disjoint union of slight inward roundings of the two
half-spheres.  The seam was chosen away from the knot, and all geometric containments are strict,
so the rounding neither changes a knot intersection nor loses the successor-box containment.
After a generic perturbation, the sphere is transverse to the transported torus except at finitely
many elementary surgery times.  At every regular time its knot intersections inject into the
disjoint event set consisting of one outer copy and two tagged cut copies, hence number at most
`156D`.

There are two cases.

1. Some regular sphere in the surgery family contains an essential torus circle.  Choose an
   innermost essential circle on that sphere.  It bounds a sphere-side disk whose other torus intersections
   are all inessential.  A zero-winding embedded torus circle lifts to a planar Jordan curve; the
   planar Schoenflies theorem fills it, and disjointness from every nonzero lattice translate
   makes the projected filling an embedded disk on the torus.  Repeated innermost-circle surgery
   replaces the sphere-side disk across these torus disks.  The finite number of intersection
   circles strictly decreases, so the process terminates at an embedded compressing disk with the
   same essential boundary and with open interior disjoint from the torus.

2. Every regular sphere in the family has only inessential torus intersections.  For any regular
   time, retain only the maximal pairwise-disjoint torus fillings.  The complement of these disks
   is obtained from a torus punctured at finitely many points: in Schoenflies coordinates, a
   compactly supported radial homeomorphism pushes a point out to the corresponding closed disk,
   and supports are chosen successively away from all other maximal disks.  The deformation from
   the identity preserves winding.  In the finitely punctured product torus, choose a first Circle
   coordinate and a second Circle coordinate missed by all punctures; the corresponding longitude
   and meridian share a basepoint, avoid every puncture, and have winding pairs `(1,0)` and `(0,1)`.
   Pushing them forward gives the unique rank-two carrier component of the sphere complement.
   Across an elementary sphere or intersection surgery the inside/outside rank can change by at
   most one, while for an inessential cut on a torus it is always either zero or two.  It is
   therefore constant through the family.  Initially the carrier is inside the outer sphere;
   finally it is inside one of the two terminal spheres.  Thus one successor half carries the full
   rank-two winding witness.

Regular planar charts descend through the product-circle covering in
`Topology/RegularLevelQuotientCharts.lean`; compact connected one-manifold classification and its
complete rotated-gradient orbits are in `Topology/PeriodicOrbitClassification.lean` and
`Topology/RegularLevelTangentODE.lean`.  Finite surgery termination is in
`Topology/InnermostCircleSurgery.lean`.  The strong planar Schoenflies source is vendored under
`Submission/PlaneSchoenflies/`; its torus-side application is in
`Topology/InessentialTorusCircleDisk.lean`.  The compactly-supported one-disk radial pushout is in
`Topology/TorusDiskPuncture.lean`, and the finite-puncture carrier and homotopy-preserving pushout
adapters are in `Topology/FinitePunctureAxisCarrier.lean` and
`Topology/FinitePunctureCarrierPushout.lean`.  The final double-bubble module uses these concrete
carriers to prove the rank-zero/rank-two alternative at regular times and its invariance across
the finitely many elementary surgery events.

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

The compressing boundary lies on one of the two half-spheres before the inessential-circle
surgeries; every surgery is performed through a disk on the torus and preserves the boundary.
After the harmless seam rounding, every boundary intersection with the knot can therefore be
charged injectively to either one outer-surface crossing or one tagged copy of a cutting-disk
crossing.  Keeping two tagged cut copies uniformly covers the two half-spheres.  The number of
available events is at most

```text
76D + 2 * 40D = 156D ≤ 160D.
```

Representativity supplies at least `min(p,q)` distinct intersections.  Under the contrary
assumption `160D < min(p,q)`, no such injection can exist.  Consequently the compression branch
of the cut alternative is impossible, and one successor half-box must carry genus.  Iterating the
`69/70` shrink contradicts local flatness, proving the desired bound.

The smooth event finsets and cardinal arithmetic are in
`SuperellipsoidDoubleBubbleSelection.lean`; reparametrization transfer, signed-root certificates,
and compression exclusion are in `ReparamCharging.lean`, `Topology/ShiftedCompressingDisk.lean`,
`Topology/SmoothEssentialSectionCircle.lean`, and `CompressionExclusion.lean`.

## Remaining kernel-level integration boundary

The numerical, coarea, compactness, winding, solid-torus, regular-level, one-dimensional degree,
and finite-surgery layers above are implemented and axiom-audited.  The final integration theorem
assembles the two finite half-sphere circle systems, the finite sequential disk pushout, and the
charged essential-circle branch into the one-step shrinking alternative.  The benchmark capstone
then chooses the supplied ambient isotopy and reparametrization and invokes the nested-box
contradiction.
