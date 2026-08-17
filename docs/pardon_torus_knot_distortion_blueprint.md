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

The literal union of the outer sphere and the cutting disk is not itself a disjoint union of
intersection circles.  At every transverse torus--seam point its intersection with the torus has
three incident half-edges: two along the outer section and one along the inward part of the cut
section.  In particular, one cannot replace one T-vertex by an embedded one-manifold inside an
isolated neighborhood, since a compact one-manifold patch has an even number of boundary
endpoints.  The actual two-surgery pairs consecutive seam vertices along an excursion arc of the
cutting section.  A narrow band containing the whole excursion has four outer endpoints, and the
moving sphere realizes the two possible pairings before and after surgery while agreeing with the
original intersection outside the band.  Ordering the finitely many seam points gives finitely
many such paired bands.

The band chart can be constructed without assuming a tubular-neighborhood theorem for arbitrary
surface arcs.  Lift one closed excursion to the angle covering plane.  Enlarge its parameter
interval slightly on both ends; the strict gap between consecutive crossings and embeddedness of
the cutting circle make this an extendible injective planar path.  Complete that path to a Jordan
circle by joining the two short access tails through the connected complement of the original
arc, resolving the connector to an injective polygonal arc.  Complete the standard horizontal
seam segment in the same way.  `TwoArcJordan` parametrizes both first arcs by the same half of the
circle, while the proved Moise regional extensions straighten each completed Jordan circle with
that exact parametrization.  Their composite is therefore an ambient plane homeomorphism taking
the standard seam segment to the lifted excursion pointwise, not merely setwise.

The product-circle covering is injective on some open neighborhood of the compact lifted arc:
this follows from local injectivity of the covering and the compact `InjOn` neighborhood lemma.
Pull that neighborhood back through the straightening homeomorphism and choose a thin rectangle
around the standard segment.  Explicit one-dimensional order homeomorphisms identify all of
`Plane` with the rectangle while fixing `[-1,1] × {0}` pointwise.  Restricting the covering to
the resulting strip gives a homeomorphism onto a transported-torus surface patch, remains inside
the automatically separated ambient band, and has exactly the required seam-core formula.  This
construction is formalized by `ExtendibleArcTubularStrip.lean` and
`SuperellipsoidGlobalBandTubularChart.lean`: it produces `GlobalBandTubularChartData` with exact
core parametrization and containment in the canonical separated band neighborhood.

In these actual band coordinates the local two-surgery has an explicit quadratic model.  On
`Q = {x² + y² ≤ 2}`, put `p = x² - 1`, `s = 1 - y²`, and
`f_t = (1-t)p + ts`.  The functions `p` and `s` agree on the frontier of `Q`; their zero sets are
respectively the two vertical and two horizontal four-port pairings.  An explicit normal tube
around the transported torus turns the graphs of `f_t` into embedded ambient patches, while a
fiberwise Möbius homeomorphism maps the initial graph to every later graph and fixes the whole
frontier.  The local graph, tube, and exact carrier equations are formalized in
`NormalTube.lean`, `FourPortMorseGraphPatch.lean`,
`SuperellipsoidGlobalFourPortMorseGraph.lean`, and
`SuperellipsoidGlobalFourPortCarrier.lean`.

After a generic perturbation, the sphere is transverse to the transported torus except at finitely
many elementary surgery times.  At every regular time its knot intersections inject into the
disjoint event set consisting of one outer copy and two tagged cut copies, hence number at most
`156D`.

There are two cases.

1. Some regular sphere in the surgery family contains an essential torus circle.  Choose an
   innermost essential circle on that sphere.  It bounds a sphere-side disk whose other torus
   intersections are all inessential.  A zero-winding embedded torus circle lifts to a planar
   Jordan curve; the
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

There is also a useful regular-band route for the all-inessential branch.  Compactness separates
the selected regular cut height `d` from the critical values of the transported-torus height
function, giving a closed regular band around `d`.  Shrink its half-width `ε` below one quarter of
the incoming box scale and truncate the convex outer superellipsoid at the two levels `d-ε` and
`d+ε`.  The resulting lower and upper closed convex bodies are disjoint, have nonempty interior,
and have embedded-sphere frontiers.

The regularized normalized gradient

```text
grad(h) / |grad(h)|^2
```

is made globally smooth and deck-periodic with a compactly supported height cutoff.  Its complete
flow has height derivative one throughout the band.  Grönwall control gives joint continuity in
time and initial point, deck equivariance descends the flow to the torus, and flowing each point
for time `d-h(x)` retracts every band component onto one central regular circle.  Hence every loop
in one middle component has winding equal to an integral multiple of that circle's winding; two
independent winding classes cannot lie there.  Consequently, whenever an honest sphere/collar
construction supplies a four-cell partition into lower, middle, upper, and exterior pieces, the
incoming carrier rules out exterior and the regular-band theorem rules out middle; connected
maximal-disk localization leaves only a child.

The two literal separated truncation spheres do *not* alone supply that four-cell partition.  Their
common outside connects the height band to the ambient exterior through the omitted strip of the
old outer frontier.  Thus an additional disjoint outer/collar barrier, or an equivalent relative
parity transition, is necessary; endpoint regularity by itself cannot hide this gap.  The
regular-band selection, cyclic-winding consequence, explicit separated endpoint spheres, and
conditional pure localization theorem are formalized in
`OrientedCoordinateRegularBand.lean`, `RegularBandCentralCircle.lean`,
`RegularBandNormalizedGradientFlow.lean`, `RegularBandCyclicWinding.lean`,
`SuperellipsoidGlobalNeckPinchRounding.lean`, `SuperellipsoidTwoLevelRegularBand.lean`, and
`RegularBandTwoLevelDichotomy.lean`.  The purely logical essential-or-child adapter is in
`SuperellipsoidTwoLevelResolution.lean`; it keeps the global four-cell partition as an explicit
geometric input.

Regular planar charts descend through the product-circle covering in
`Topology/RegularLevelQuotientCharts.lean`; compact connected one-manifold classification and its
complete rotated-gradient orbits are in `Topology/PeriodicOrbitClassification.lean` and
`Topology/RegularLevelTangentODE.lean`.  Finite surgery termination is in
`Topology/InnermostCircleSurgery.lean`.  The strong planar Schoenflies source is vendored under
`Submission/PlaneSchoenflies/`; its torus-side application is in
`Topology/InessentialTorusCircleDisk.lean`.  The compactly-supported one-disk radial pushout is in
`Topology/TorusDiskPuncture.lean`, and the finite-puncture carrier and homotopy-preserving pushout
adapters are in `Topology/FinitePunctureAxisCarrier.lean` and
`Topology/FinitePunctureCarrierPushout.lean`.  The final double-bubble layer combines these
concrete carriers with the paired-band local models.  At a regular time it gives the
rank-zero/rank-two alternative; across one paired-band surgery it proves that the rank-two side
cannot disappear without producing an essential intersection circle.  Finite induction over the
ordered bands transports the carrier from the initial outer sphere to one terminal half-sphere.

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
finite sequential disk-pushout, canonical maximal-disk, and finite-surgery layers above are
implemented and axiom-audited.  So are the finite heterogeneous parity induction, the exact
extendible-arc tubular strips, the transported-torus band charts, the quadratic four-port normal
graphs, and charging transported from the original outer/cut barrier loops to smoothed stage
loops through transverse continuation.

The endpoint torus sections are now decomposed into circles.  The lower and upper outer gaps and
the inward cut gaps have exact closed carrier formulas, including cyclic wraparound and seam
endpoints.  Finite alternating endpoint systems are split into quotient cycles; their genuine
nonempty path concatenations are embedded circles, distinct quotient cycles have disjoint ranges,
and finite closed-arc isolation upgrades the exact carrier formulas to the required ambient local
`V` germs.  Seam-free outer and cut circles are separately classified by their constant strict
side sign.  Thus the remaining set-theoretic completion into the exact lower and upper truncated
sphere sections is bookkeeping rather than a new geometric hypothesis.

The unresolved geometric input lies one level later, in the all-inessential four-port transition.
The literal pre- and post-resolution circles agree on their outside arcs, so they cannot
simultaneously be the three disjoint boundary components of a pair of pants.  They must first be
separated by small *tangential* self-isotopies of the transported torus.  The already constructed
ambient normal tube cannot provide these: a base-fixed normal-fiber map which returns the zero
slice to the torus is pointwise the identity on that slice.  What is needed is a relative regular
neighborhood theorem for the labeled global four-port theta graph, compatible with its prescribed
vertex charts.  It must produce two supported torus isotopies, three disjoint parallel endpoint
circles, their annular sweeps, and a connected regular-closed pair-of-pants trace whose frontier is
exactly those circles.

Canonical Schoenflies disks for the three zero-winding boundary circles are already proved
laminar.  Their open sides, closures, and frontiers give the required local side alternative, and
finite-puncture connectivity derives the all-exterior complement theorem.  The remaining global
surface fact is the standard pair-of-pants first-homology statement: every loop winding in the
trace is an integer combination of the three boundary windings.  Since all three boundary
windings vanish, one canonical disk contains the entire trace and hence the actual label-change
locus.  The transition may be pre-sided or post-sided; the finite heterogeneous parity sequence
has been generalized to allow that choice at every elementary move.  The essential branch already
feeds the innermost sphere-disk surgery and transverse charging continuation.  Once the relative
theta-graph neighborhood and pair-of-pants winding-generation lemmas are supplied, the existing
finite transition, charging, nested-box, and capstone layers close the benchmark theorem.
