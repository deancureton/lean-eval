# Proof blueprint for Pardon's torus-knot distortion bound

## Target

For positive coprime integers `p,q`, every smooth knot ambient-isotopic, with orientation, to the
standard `(p,q)` torus curve has

\[
  \operatorname{distortion}(K) \geq \frac{\min(p,q)}{160}.
\]

The Lean statement uses `ℝ≥0∞`; the proof first handles the case of finite distortion and then
transfers the resulting real inequality back to `ℝ≥0∞`. The infinite case is immediate.

## 1. The shrinking contradiction

Assume

\[
  160\,\operatorname{distortion}(K) < \min(p,q).
\]

The transported standard torus carries two based loops of independent winding. Start with an
oriented box carrying those loops. For every positive carrying box, construct a successor box
whose scale is at most `69/70` of the old scale and which again carries two independent loops.
Local flatness gives a uniform positive lower bound for the scale of any carrying box. Iterating
the successor construction therefore gives a positive sequence bounded below while shrinking
geometrically, a contradiction.

This reduction, including the extended-real bookkeeping and infinite iteration, is formalized in
`PardonReduction`, `Shrinking`, `NestedCarrier`, and `SuperellipsoidPardonGeometricStep`.

## 2. The counted double bubble

Inside a carrying box choose a smooth superellipsoid outer level and a regular coordinate cut.
The coarea bounds are

\[
  \#(K\cap\text{outer sphere}) < 80D,
  \qquad
  \#(K\cap\text{cut disk}) < 40D,
\]

where `D = distortion(K)`. The cut disk is charged to both children, so the weighted event count
is strictly less than

\[
  80D + 2\cdot40D = 160D.
\]

Sard, Fubini, seam transversality, compactness, and the exact smooth intersection-circle
classifications needed for these choices are already formalized in the `Coarea` and
`Superellipsoid*` modules.

## 3. Exact finite torus sections

The outer sphere and cut disk meet the transported torus in finite regular circle families.
Crossings are cyclically ordered. Alternating outer gaps and inward cut gaps form a finite
degree-two graph, whose cycles give the exact lower and upper truncated-sphere sections.

The formal chain constructs:

- smooth outer and cut circle parametrizations;
- exact closed half-gap coverage, including inactive seam-free circles;
- finite alternating cycle decompositions;
- embedded circle realizations with exact local V-shaped seam germs;
- exact lower and upper finite torus sections.

The endpoint result is exposed by `SuperellipsoidCanonicalTruncatedSphereSection`.

## 4. Canonical four-port charts

Near each paired seam excursion, the normalized height gradient supplies a complete flow collar.
At two selected regular heights, the flow slice crosses the outer barrier exactly twice. The two
crossings vary continuously with height. Filling between those crossing graphs gives an explicit
embedded square whose midline is the original cut seam and whose boundary is the completed
three-path theta graph.

Planar Jordan recognition proves that the lower-upper cycle is the outer theta cycle. The exact
three-path ambient-extension theorem therefore yields a seam-fixing plane homeomorphism to the
standard four-port model. Pulling the open tubular strip back by this homeomorphism gives exact
canonical band charts:

\[
  x\in\text{analytic barrier}
  \quad\Longleftrightarrow\quad
  \text{chart coordinate}(x)\in
  (\text{left edge}\cup\text{right edge}\cup\text{seam}).
\]

The concrete constructor is `centralHeightFlowArcExactness`. Consequently exact chart geometry is
no longer a field of the canonical Pardon witness.

## 5. One quadratic flip

In standard strip coordinates, changing one Boolean smoothing is the quadratic four-port move.
The six outside and local edges form a theta graph. Its coherent lift to the covering plane has a
canonically selected outer cycle. The quadratic label-change lens lies in the bounded rectangular
face. Hence all three affected boundary circles and the entire label-change locus lie in the disk
bounded by the selected outer cycle.

If every endpoint circle is inessential, canonical laminar maximality enlarges that disk to a
maximal disk of whichever endpoint stage contains the selected outer circle. Thus each flip gives
either a forward or a reverse `FiniteElementaryDiskSideCover`. The side may vary from flip to
flip; no false pre-sided nesting assertion is used.

This stage-side alternative and its finite aggregation are formalized in
`FourPortSixEdgeCanonicalDiskSide`, `FourPortQuadraticLabelChangeContainment`,
`FourPortSixEdgeEndpointSystemAttachment`, and `DiskLocalizedParityTransition`.

## 6. The finite-stage dichotomy

Audit every regular sphere stage.

- If some intersection circle is essential, the sphere-side disk forces an axis-slope circle.
  Regular continuation transports its event charging back to the counted analytic barrier. The
  torus-knot intersection certificate then requires at least `min(p,q)` charged events, contrary
  to the strict `160D` count.
- If every intersection circle is inessential, the heterogeneous stage-side covers propagate the
  rank-two carrier through the entire Boolean flip sequence. At the terminal separated two-sphere
  stage, the carrier must lie in the lower or upper child cell.

Either branch therefore gives a lower or upper child carrying two independent based loops. Each
child lies in a successor box of scale at most `69/70` of the parent, closing the shrinking step.

## 7. Exact remaining construction boundary

The ambient support for one quadratic move is now explicit. The standard normal tube is proved
to be an open embedding by identifying its range with the gauge shell

\[
  1/4 < \operatorname{tubeGauge} < 9/4.
\]

Over every canonical open band chart, the closed quadratic base disk times the closed normal
interval is therefore a compact ambient patch with open interior. The boundary-fixed Mobius
fiber move extends by the identity to an ambient homeomorphism of `R3`, and it carries the exact
time-zero vertical graph to the exact quadratic Morse graph at every time. These constructions
are isolated in `NormalTubeOpen`, `FourPortClosedTubeHomeomorph`, and
`FourPortChartClosedTubeHomeomorph`.

`AmbientSphereLocalGraphMove` then transports the source sphere and its open inside cell. The
frontier theorem follows functorially from the ambient homeomorphism, while a direct set
calculation gives the new exact torus intersection as the unchanged outside section union the
chosen local four-port section. Sphere-side filling disks are subsequently derived by the
existing finite-circle-section machinery; they are not additional geometry fields.

The remaining local geometric theorem must assemble a common transverse bicollar over each
compact band and then normalize the *actual source sphere sheet* to the time-zero graph, relative
to a slightly larger support patch. Ordinary sphere--torus transversality does not say that the
sphere is a graph in the fixed radial-normal tube. `SuperellipsoidNormalShearLocalGraph` now proves
the pointwise remedy: the normalized tangential gradient gives a canonical shear direction whose
vertical derivative is strictly positive, and the scalar implicit-function theorem then gives an
exact local graph. The direction varies continuously on the regular base; its polynomial normal
weight makes it smooth after the standard regularized reciprocal is installed. The remaining work
is to restrict the resulting Euler shear to a uniformly thin compact tube. The subsequent fiber
normalization fixes the torus zero slice, so it preserves the endpoint torus section and parity
labels. Once this bicollar attachment is assembled, the already-constructed ambient homeomorphism
supplies the corresponding middle regular sphere stage automatically.

The implementation route is now narrow:

1. Pull the explicit open normal tube back to a canonical band. Use the canonical direction from
   `SuperellipsoidNormalShearLocalGraph`; tangential regularity makes its vertical derivative
   positive. Compactness bounds the derivative of this field. Then
   `SmallLipschitzNormalShear` proves that `(u,s) |-> (u+s v(u),s)` is a closed embedding whenever
   the normal interval is thin enough that `epsilon K < 1`; the canonical choice
   `epsilon = 1/(2(K+1))` satisfies this inequality and is positive.
   `SuperellipsoidNormalShearField` packages the intervening analytic step: compactness gives a
   positive lower bound for the tangential derivative norm on one fundamental zero set, the
   regularized reciprocal extends the canonical direction to a smooth deck-periodic field, and
   the periodic derivative bound supplies a global Lipschitz constant. For a compact base inside
   the retained open covering sheet, `SmallLipschitzNormalShear` then chooses a still smaller
   positive radius so every sheared base point remains in that same sheet while the full shear is
   a closed embedding. `NormalShearTubeBicollar` composes this shear with the transported normal
   tube, and `SuperellipsoidNormalShearBicollar` packages the resulting compact ambient closed
   embedding together with its exact pointwise zero-slice identity.
   The zero-slice derivative of this variable Euler shear is exactly the frozen linear shear used
   by the implicit-function theorem. Deck reduction therefore identifies the global field with
   the canonical direction at every lifted outer-level zero and supplies a local graph from the
   same field at every such point. `SuperellipsoidBandNormalShearBicollar` applies this package to
   the retained covering-plane lift of each canonical band: the compact four-port disk lies in one
   open covering-injective sheet, and one bicollar field supplies the local graph neighborhoods at
   all of its outer-level zeros. `SuperellipsoidCanonicalHeightFlowOpenBand` retains that open
   covering sheet after precomposing its plane coordinate with the seam-fixing filled height-flow
   straightener. Consequently the exact filled-theta chart and the normal-shear bicollar now refer
   to the same reparametrized band, rather than to two unrelated choices of tubular chart.
2. Apply the parameterized implicit-function theorem and compactness near the outer zero set.
   Compactness gives a finite cover by exact graph neighborhoods for the one global field. The
   common strictly positive vertical derivative makes every fiber in a uniform interval strictly
   increasing, so the restricted local graphs agree on overlaps and glue continuously on the open
   union of their domains. This is the exact result supplied by
   `SuperellipsoidBandNormalShearBicollar`.

   This local result does **not** put the full closed four-port patch in the graph domain. The core
   of a canonical band is the entire inward cut excursion, while the outer sphere meets that core
   only at its seam endpoints. The excursion interior can lie deep inside the outer body, so no
   shrinking of neighborhoods of the outer zero arcs can cover the two-dimensional patch. The
   missing construction is therefore a relative disk-sheet attachment, not another compactness
   argument: build an embedded source disk over the filled height-flow theta, attach its frontier
   to the unchanged outside sphere sheet, and prove that the resulting closed surface is an
   embedded sphere bounding an open cell. Its local normal height must have the time-zero vertical
   zero set. Only after this source disk has been constructed does the fixed-zero graph
   normalization apply. `AmbientSphereLocalGraphMove` now contains the exact relative-patching
   adapter: a `RelativeSphereBandPatchData` whose replacement image is the time-zero graph and
   whose outside sheet is disjoint from the compact tube patch automatically produces the
   normalized source-sphere record consumed by the ambient move. Thus the remaining theorem no
   longer needs to repeat the global carrier set calculation; it only has to construct the
   relative source patch, its open inside cell, and the boundary identity. Alternatively, an
   ambient spanning-disk normalization can use `CanonicalBandSourceSphereGraphData.ofAmbientImage`;
   the inside cell and frontier identity then follow functorially, leaving only the ambient
   homeomorphism and its exact local/outside sheet equations.

   The quadratic model provides a canonical local attachment without an arbitrary cap. The
   time-zero and time-one graph disks agree on the entire circle `x^2+y^2=2`, while their interiors
   are disjoint because the height difference is `(2-x^2-y^2)/4`. Their union is the boundary of
   the coordinate lens

   \[
     (x^2-1)/4 \le z \le (1-y^2)/4.
   \]

   This lens is compact, convex, and has nonempty interior: it is the intersection of the convex
   sublevels `x^2-4z <= 1` and `y^2+4z <= 1`. Thus convex gauge rescaling supplies its sphere
   parametrization. `FourPortMorseEmbeddedDisk`, `FourPortMorseLens`, and
   `RelativeSphereEmbeddedDiskPatch` isolate respectively the endpoint disks, their exact common
   boundary/disjoint-interior geometry, and the relative patch adapter. The convex recognition and
   sphere parametrization are implemented by `FourPortMorseLensSphere`.
   `FourPortMorseLensChartSphere` then embeds the full lens in the canonical closed band tube and
   transports that sphere to ambient three-space, with its two graph faces definitionally equal to
   the time-zero and time-one global Morse disks. The remaining recognition step is to identify the
   lens frontier with those two disks and the image of its strict interior as an ambient open cell.
   For that recognition, use the two vertical shear homeomorphisms

   \[
     (u,z) \mapsto (u,z-p(u)/4), \qquad
     (u,z) \mapsto (u,s(u)/4-z).
   \]

   They identify the lower and upper lens inequalities with the pullback of the closed half-line
   `[0,infinity)`. Homeomorphisms preserve interiors, while the interior of that half-line is
   `(0,infinity)`. Therefore the interior of the lens is exactly the simultaneous strict-inequality
   region, and the closed-set identity `frontier K = K \ interior K` makes its frontier exactly the
   union of the two graph faces. The chart embedding is an open embedding on this strict region, so
   its image is the required ambient-open inside cell; closed-embedding injectivity transports the
   frontier identity without introducing any extra boundary points.
3. Orient the common transverse fiber so that the actual graph height `g` and the time-zero
   quadratic height `p` have the same sign off their common regular zero set.  The parameterized
   Hadamard factorization along the two vertical zero arcs then gives a continuous positive
   quotient `rho` with `g = rho * p`, including at the zero arcs by the ratio of transverse
   derivatives.  Shrink the tube once so both graphs remain strictly between its faces.
4. On each positive half-fiber use

   \[
     h_k(s)=\frac{k s}{1+2(k-1)s},
   \]

   and use its odd reflected formula on each negative half-fiber.  Both formulas fix `0` and the
   corresponding endpoint `+/-1/2`; they are strictly increasing for `k>0`, and their inverses
   are obtained by replacing `k` by `k^{-1}`.  Choosing

   \[
     k=\frac{p(1-2g)}{g(1-2p)}
   \]

   on the positive side (with the reflected `1+2g`, `1+2p` formula on the negative side) sends
   `g` exactly to `p`.  The positive quotient from the previous step supplies the continuous
   limiting value at `g=p=0`.  Thus the family is jointly continuous across the zero slice and
   fixes `-1/2`, `0`, and `1/2` pointwise.  Conjugate it through the common bicollar and extend it
   by the identity across the slightly larger patch.  Fixing the zero slice preserves the
   transported torus and hence the endpoint torus section and parity labels.

   In the implementation the positive and negative formulas are combined before the continuity
   proof.  Writing `g = rho * p`, the single scale

   \[
     k(\rho,p)=\frac{1}{\rho}
       \frac{1-2\rho |p|}{1-2|p|}
   \]

   is positive whenever both graph heights lie strictly between the tube faces.  It specializes
   to the displayed positive formula and its negative reflection, extends at `p=0` with value
   `rho^{-1}`, and equals one wherever `rho=1`.  The reusable algebra and continuity package is
   `FourPortGraphScaleNormalization`; `FourPortFixedZeroChartHomeomorph` conjugates the resulting
   bundle map into the chosen ambient chart and extends it by the identity.

   `FourPortRelativeGraphHomeomorph` also gives a simpler boundary-fixed Mobius map between any
   two continuous graph heights which agree on the base frontier. This is enough for exact carrier
   normalization and avoids the quotient factorization. It is not a replacement for the
   fixed-zero construction in the canonical chain: an arbitrary fiber map can move the torus and
   hence change the inside label before the first audited stage. The fixed-zero normalizer now has
   an exact global theorem fixing every transported-torus point, and finite composites inherit an
   exact inside-membership equivalence there.
5. Apply `AmbientSphereLocalGraphMove`, compose the moves in the pairwise-disjoint band supports,
   and classify the resulting finite resolved carrier into its embedded circle components.

The reusable-library audit found the needed local pieces but no theorem packaging this bicollar.
Pinned Mathlib supplies `implicitFunctionOfProdDomain` and its derivative/continuity theorems.
The repository supplies the complete normalized torus height flow, the explicit transported open
normal tube, compact-open injectivity lemmas, and boundary-fixed extension by identity. Neither
the pinned checkout nor current upstream Mathlib exposes a tubular-neighborhood theorem for an
embedded hypersurface or a bicollar theorem compatible with a prescribed zero slice. The new
construction should therefore compose these existing primitives rather than introduce another
abstract collar premise.

The resulting middle Boolean family must then construct:

1. a finite family of embedded spheres;
2. the compatible simultaneous composition of the disjoint local moves;
3. the exact transported-torus intersection as the resolved Boolean circle family;
4. endpoint identifications with the initial outer sphere and separated terminal children;
5. regular continuation/charging data for every essential stage circle.

The local quadratic charts, ambient patch moves, endpoint circle systems, terminal sections, and
all-inessential disk-side covers are already available. The remaining work is the relative
source-disk attachment and its compatible composition over the disjoint bands. Pointwise
outer-sphere graph neighborhoods are useful only at the attachment arcs; they are not a
substitute for the spanning disk. The filled height-flow square already supplies the canonical
planar disk and exact theta frontier, while `TriangleDiskEmbeddingRecognition` supplies the disk
recognition step. What is still missing is the ambient gluing theorem identifying the
complementary outside sheet and proving that the glued closed surface is a sphere bounding an
open cell. The moved sphere-boundary identification is already derived once that source sphere
exists. The final implementation must prove these attachment facts rather than assume a
`PairedBandMovingSphereCollarData` or a conclusion-shaped parity transition.

The correct global assembly uses `SuperellipsoidCanonicalChainSideCoverAxisData`: the initial
outer sphere and separated terminal children are the fixed endpoints, while the Boolean
moving-sphere resolutions are only the middle stages. The final neck pinch may therefore be
performed away from the transported torus and supplied as a torus-invisible sided transition;
it is not falsely required to be another quadratic four-port flip.

The flared external cap in `FourPortMorseExternalCapCoordinate`,
`FourPortMorseExternalCapGlobal`, and `FourPortMorseExternalCapAttachment` validates the local
relative-disk mechanism: its bottom is exactly the time-zero Morse disk, its complementary sheet
misses the compact patch, and the resulting sphere bounds an explicit ambient-open cell. The
attachment now feeds `CanonicalBandSourceSphereGraphData` and the boundary-fixed endpoint
homeomorphism directly, so both moved endpoint spheres inherit exact frontier and torus-section
formulas. It is not by itself a middle stage for the global argument. Its complementary torus
section is a synthetic section in one covering-injective strip, not the unchanged outer/cut
barrier outside the band. The global construction must attach the same local disk to the actual
three-page outside sheet, or prove a disk-sided transition from that sheet. This agreement cannot be
replaced by taking an independent cap sphere for every band, because the resulting parity cell
would not agree with the parent stage away from the band supports.

The component count need not change during the Boolean moves. The intended middle family is a
single dumbbell sphere: begin with the outer sphere, replace its local disk in each disjoint
band, and retain one common outside sheet throughout. After every band has the child pairing, a
final change supported away from the transported torus separates that dumbbell into the two
canonical terminal spheres. Thus the remaining attachment theorem has a precise relative form:
cut pairwise-disjoint parameter disks from the outer sphere, identify their boundary collars
with the time-zero Morse disks, glue the selected Morse disks to the unchanged complement, and
prove that the resulting carrier bounds an open cell. The existing ambient four-port
homeomorphisms then supply all Boolean choices without changing the common outside sheet.
Neither `SuperellipsoidGlobalNeckPinchRoundingData` nor the standalone external cap contains
this relative identification.

`FiniteDisjointAmbientSphereMoves` isolates the subsequent finite composition. Starting from one
honest common source sphere and open inside cell, it composes the pairwise-disjoint ambient moves
in canonical finite order, transports the inside cell, proves every stage is its exact frontier,
and keeps the complement of all supports pointwise fixed. Consequently the unresolved geometry
is only the construction of that common normalized source sphere; no additional global
composition or Jordan-boundary theorem is needed after it is supplied.

`FiniteDisjointAmbientSphereCarrier` derives the corresponding exact carrier formula: every
stage is the common outside sheet together with the source or target local sheet selected at each
band. Its torus-section adapter then turns local source/target intersection equations into the
exact global transported-torus section. Thus the common-source constructor need only establish
the one outside section, the pairwise-disjoint ambient patches, and the time-zero local graph in
each patch; all Boolean carrier equations follow formally.

`FiniteCanonicalBandCommonSource` specializes this to the canonical charts. Global injectivity of
the transported normal tube and the already disjoint band neighborhoods prove that the compact
ambient patches are pairwise disjoint, so disjointness is no longer an attachment premise. The
remaining record contains exactly one source sphere/open cell, its time-zero local-sheet equations,
and its unchanged outside torus section.

The common sphere need not be glued as a new surface. `FiniteCanonicalBandOuterNormalization`
starts with the known outer sphere and one boundary-fixed ambient normalizer in each canonical
band. Their disjoint finite composite is automatically a sphere bounding the transported outer
inside cell. Its last-stage carrier intersects each patch in the normalized time-zero sheet and
agrees with the outer sphere off all patches. The geometric task is therefore local: construct the
outer-sheet graph and its fixed-boundary normalization to the Morse graph in each band.

There is also a strictly more geometric endpoint for that construction.
`FiniteCanonicalBandOuterAmbientAttachment` asks for one relative ambient homeomorphism of the
actual outer sphere, fixed pointwise on the transported torus, whose image has the time-zero Morse
sheet in every compact band. It derives the common source, its transported inside label, its full
outer torus trace, and the empty initial transition. This avoids the stronger and generally false
claim that the analytic outer boundary is a normal graph over the entire four-port disk. The
remaining disk-replacement theorem should construct this relative ambient homeomorphism directly.
The canonical specialization fixes the source sphere to
`outerSuperellipsoidSphereData.sphere` and the source cell to the interior of the closed
superellipsoid, so neither object nor either endpoint identification remains a caller premise.

The normal-shear local graph theorem does not construct this homeomorphism.  Its exact graph
domain may be a disconnected union of neighborhoods of the two outer branches, whereas the
quadratic replacement sheet is one connected disk.  A reparametrization cannot place that disk
inside the disconnected graph domain.  Consequently the factored-graph modules remain useful
only when a genuine full source disk has separately been found; they do not replace the relative
disk-attachment theorem.  Nor can the missing move be supported entirely in the compact normal
patch: such a homeomorphism preserves the patch setwise and hence preserves the topology of the
outer carrier's intersection with it.  The relative replacement must select a connected outer
disk whose bridge extends outside the compact patch, move it through a larger torus-relative
neighborhood, and leave only its time-zero Morse subdisk inside the compact patch.

After the common source exists, no further sphere-side topology is needed to form the audited
middle stages. `FiniteCanonicalBandPrefixRegularStages` takes only a finite embedded-circle
classification of each exact prefix torus section and an event container. It derives the singleton
moved-sphere family, transported open inside cell, exact torus intersection, sphere-side filling
disks, and the complete finite regular-stage family. This separates the remaining circle
classification and charging work from the already formal finite ambient composition.

The fixed-zero normalization also gives both endpoint invariants needed by the full chain: its
finite composite preserves outer-inside membership and the outer carrier trace on the transported
torus. `TorusInvisibleElementaryDiskSideCover` turns equality of those two torus data into the
zero-move sided cover. Hence the initial outer-to-common-source normalization and the final
torus-disjoint neck pinch require no artificial quadratic move or extra disk-localization premise.
`FiniteCanonicalBandFactoredInitialTransition` derives the initial cover directly from the
fixed-zero factored normalization and the canonical outer stage entry.

The initial adapter only needs equality of the two ambient carrier traces on the transported
torus, together with equality of their torus-side inside labels.  It does not identify the
ambient sphere families themselves.  This permits a synthetically attached common source sphere
once its trace and parity side have been proved equal to the canonical outer stage.

There is a sharper route which removes this last three-dimensional attachment from the charged
axis argument.  `ReducedTorusParityAxis` records only the data actually used there: each stage's
finite winding circles, its boundary subset of the transported torus, and its two open parity
cells.  In an all-inessential transition the canonical maximal-disk pushout is summarized by its
connected rank-two complement and the theorem that every loop in the disk union has zero winding.
The carrier-propagation proof then runs verbatim, while an essential stage is still ruled out by
the existing charged nonzero-axis circle.  The adapter from the old sphere system verifies that
this reduced interface loses no logical content.

`ReducedTorusCircleStages` removes the remaining stage-family plumbing: an exact finite torus
circle section together with an open region having precisely that frontier gives a reduced stage,
and a natural-number family of those data gives the exact sequence consumed by the axis theorem.
Thus ambient sphere parametrizations, sphere-side filling disks, and event regions are absent
from the all-inessential construction boundary.

`ReducedTorusCircleCore` also removes the ambient sphere system from the canonical-disk argument.
For any finite pairwise-disjoint family of zero-winding torus circles, it constructs the canonical
Schoenflies disks, selects the inclusion-maximal laminar disk images, derives pairwise-separated
supports, and applies the finite sequential puncture pushout.  The resulting complement is
connected and carries two independent winding loops, while every loop contained in the maximal
disk union has winding pair `(0,0)`.  This is exactly `ReducedInessentialTorusCoreData`, obtained
directly from the finite circle family.

`ReducedTorusCircleTransitions` turns the local disk-side geometry into the complete reduced
transition sequence.  At each move the canonical core may be selected from either endpoint.  The
chosen endpoint boundary is covered automatically by its circle disks; the geometric input only
has to place the newly introduced boundary patch and the actual label-change locus in one chosen
endpoint disk.  Forward and reverse covers both construct the same forward parity transition,
and a cover for every prefix step plus the terminal two-cell partition constructs
`ReducedAllInessentialResolution` directly.

The prefix update itself is reduced by `OpenRegionLensAttachment` to two local face equations.
For open sets `A` and `L`, it proves
`frontier (A ∪ L) = (frontier A \ L) ∪ (frontier L \ A)` and proves that the label-change locus
is contained in `L`.  Therefore one band step needs only identify the old face swallowed by the
explicit lens and the new face exposed by it; no global frontier equality is taken as an input.

To complete this route, construct the reduced prefix stages directly from the canonical exact
circle sections.  Start with the outer-body label on the torus and toggle the explicit disjoint
four-port lens at each prefix.  The exact endpoint graph equations give the boundary partition;
the lens openness theorem gives the open cells; and the raw-theta disk-side results give each
inessential transition core.  The final prefix label must then be identified with the two
separated terminal child cells.  None of these steps requires an ambient middle sphere or a
sphere-side filling disk.

Once this middle family is built, its chain-side-cover adapter gives
`SuperellipsoidFiniteStageSideCoverAxisData`. Apply
`pardonTarget_of_superellipsoidFiniteStageSideCoverAxisData`, and use the ambient-isotopy and
circle-reparametrization witnesses from the benchmark hypothesis.

The reduced route now bypasses that ambient adapter entirely.  A finite entry type records one
exact torus-circle section and one open region with that section as frontier.
`ReducedTorusCircleStageGeometry.ofEntries` extends the `Fin (n+1)` family by its terminal entry,
so the audited finite interval agrees definitionally with the concrete entries.
`ReducedTorusBooleanStages` evaluates these entries along the canonical one-flip-at-a-time Boolean
prefix and turns an indexed sided cover for every flip into the full reduced transition sequence.

`SuperellipsoidReducedBooleanAxisIntegration` is the quantitative capstone for this route.  Given
the reduced Boolean entries, their per-flip sided covers, terminal cells, and essential-circle
charging transports, it proves the lower-or-upper child alternative and runs the complete Pardon
shrinking contradiction.  No ambient middle sphere, filling disk, or moving-sphere event region
occurs in this capstone.

The remaining construction is consequently two-dimensional and explicit.  For every prefix one
must decompose the resolved carrier into finitely many embedded torus circles and prove that it is
the frontier of the recursively updated open parity region.  The initial carrier is the classified
outer-circle family.  Each successor changes one standard four-port pairing; the fixed outside
pieces connect the four support ports, and the selected vertical or horizontal local paths close
them into a finite degree-two graph.  The existing `FiniteAlternatingEndpointSystem` construction
then gives the circle maps, exact carrier union, and pairwise disjointness.  What is not yet
packaged is the extraction of those fixed outside port-to-port paths from the canonical outer
circle parametrizations and the exact chart-support equation.  Once that extraction is proved,
the local lens frontier identity supplies the new open region, and the already validated raw-theta
outer-face theorem supplies the forward-or-reverse disk-sided cover.

`BooleanFourPortLocalPairing` now removes the finite matching combinatorics from that boundary.
The four ports of every band are labelled by side and level.  At a false bit, the local perfect
matching fixes the side and joins the two levels; at a true bit, it fixes the level and joins the
two sides.  Combining this explicit matching with any fixed outside perfect matching gives the
exact finite alternating endpoint system for every Boolean prefix.  Together with
`ReducedTorusAlternatingStages`, this means the remaining circle-stage input is only one fixed
outside endpoint pairing and its embedded paths, plus the local chart-path incidence and carrier
equalities.  Circle parametrization, quotient-cycle enumeration, pairwise disjointness, exact
carrier unions, Boolean evaluation, and the reduced Pardon axis are all already derived.

`BooleanFourPortLocalPaths` realizes that local matching in the actual paired seam-band charts.
It labels each abstract port by the corresponding chart corner and constructs the dependent path
family by the two vertical chart arcs for `false` and the two horizontal chart arcs for `true`.
The endpoint equalities are proved explicitly before transporting the paths, so no conclusion is
hidden in a typing cast.  It remains to combine these local paths with the fixed outside paths and
prove the resulting closed-arc incidence: same-colour paths are disjoint and an outside/local
intersection is exactly their common labelled port.

`BooleanFourPortLocalIncidence` discharges the choice-dependent half of that statement: every
local path is injective, distinct local paths are disjoint, and each local range lies in its
band support.  `FiniteAlternatingAmbientTorusCircleSection` then removes an otherwise awkward
subtype duplication.  An ambient alternating system whose two path families lie on the
transported torus lifts canonically to the exact finite torus-circle section used by the reduced
axis argument.  The remaining outside construction may therefore use the literal ambient
canonical barrier arcs and only has to prove their torus containment and exact intersections
with the four local paths.

`SuperellipsoidCanonicalBooleanOutsidePairing` now constructs the fixed outside perfect matching
without a cardinality premise.  The lower and upper central outer-gap endpoints each enumerate
the seam; the cut-gap enumeration converts every seam vertex to its unique band and side, and the
lower/upper summand becomes the level bit.  `SuperellipsoidCanonicalBooleanOutsidePaths` constructs
the exact seam-to-corner branch for every such endpoint and proves pointwise transported-torus
membership.  One cannot concatenate these branches with the untrimmed seam-to-seam outer gap:
that walk retraces both branch segments and is not injective.

`SuperellipsoidCanonicalOuterGapTrim` now performs the required extraction.  Each chart corner has
a canonical parameter strictly inside its complete outer gap; the retained path is the genuine
subpath between the two parameters.  These retained paths are injective, lie on the transported
torus, and are pairwise disjoint, including between the lower and upper families.  Moreover each
seam-to-corner chart branch is proved to be exactly the corresponding endpoint subpath of the
complete outer gap, rather than merely a subset of it.  The remaining outside-stage fact is the
exact endpoint-only intersection of a retained path with each selected local vertical or
horizontal chart path.  This now reduces to interval intersection for the endpoint subpaths and
the standard chart-support incidence; no new global circle geometry remains in that step.

That endpoint-only intersection is now complete, so
`canonicalBooleanOutsidePathData` unconditionally supplies the fixed matching, all local Boolean
matchings, their exact incidence, and the resulting finite embedded torus-circle section.

`PeriodicRegularSublevelFrontier` and `SuperellipsoidReducedInitialRegion` construct the initial
open parity region directly: the strict superellipsoid sublevel on the quotient torus is open and
its relative frontier is exactly the selected regular outer section.  The filled height-flow
square has also been upgraded from a boundary construction to an exact disk construction.
`image_interior_centralConnectorUnitSquare_eq_inside` identifies its open square with the bounded
theta face, while the canonical ambient theta homeomorphism carries the closed face to the
standard four-port rectangle.

Consequently `SuperellipsoidCanonicalReducedRegions` now defines, for every band, a closed
four-port lens and its open interior on the transported torus.  The lens is compact and closed,
its frontier is exactly the charted rectangle frontier, the closed lens lies in the closure of
the initial parity region, and its open interior lies strictly inside that region.  For every
Boolean choice, removing the selected finite closed lens union therefore gives an explicit open
reduced region.  The exact frontier theorem is now complete for every Boolean choice: selected
vertical faces disappear, selected horizontal faces appear, and the trimmed outside paths give
the unchanged outer carrier away from the lenses.  Reindexing its exact finite circle section
constructs `canonicalBooleanReducedStageData`, the full reduced Boolean stage family.

The successor geometry is also exact at the set level.  Updating a false bit to true adds exactly
one closed lens to the removed union, so the new region is the old region minus that lens and the
whole label-change locus lies in it.  The new boundary is contained in the old boundary plus the
horizontal face, and conversely the old boundary is contained in the new boundary plus the
vertical face.  `FourPortSixEdgeReducedDiskSide` combines these facts with the existing planar
outer-face theorem and directly constructs the forward-or-reverse `ReducedCircleStageSideCover`;
no ambient sphere family appears.

The remaining per-flip construction is therefore precise: extract the six-edge graph's two
outside routes from the affected quotient cycles of the finite alternating endpoint system,
identify its vertical and horizontal edge unions with the canonical band faces, and attach the
selected outer graph circle to its ordinary index in the corresponding reduced endpoint family.
After that, the all-inessential branch still needs the all-true reduced region split into its two
open terminal cells.  The essential branch separately needs the axis-circle and transported
charging packages for the canonical quotient circles.  These are the only remaining inputs to
`SuperellipsoidReducedBooleanAxisData` before the final benchmark theorem can invoke its complete
Pardon capstone.

The affected-cycle extraction no longer depends on the arbitrary quotient representative.
`FiniteAlternatingArcCycleCut` cuts an alternating quotient cycle at any specified edge and proves
that the selected edge and its complementary nonempty concatenation form an embedded two-arc
circle with exact range.  `BooleanFourPortCycleCut` applies this to either local edge of one
four-port band, and `SuperellipsoidCanonicalBooleanCycleCut` proves that the union of the two
selected local-edge ranges is exactly the canonical parallel face before the flip and exactly the
canonical surgery face after it.  Thus the two complementary outside routes and both local faces
are now canonical and exact.  The remaining six-edge step is purely the split-or-merge assembly:
determine on which endpoint the two selected local edges lie in distinct quotient components,
combine their two complementary paths with the opposite pairing, and identify the selected outer
cycle with the corresponding endpoint-family disk index.
