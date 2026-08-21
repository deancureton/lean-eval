# Pardon torus-knot distortion: proof and implementation blueprint

## Target

For positive coprime natural numbers `p` and `q`, let `K` be a smooth knot ambient-isotopic,
through an orientation-preserving ambient isotopy, to the standard `(p,q)` torus knot.  The Lean
target is

```lean
(1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K.
```

The formal proof follows Pardon's shrinking-box argument rather than importing the published
surface theorem as a black box.  Assuming the strict opposite inequality, it constructs a
strictly shrinking sequence of oriented boxes that all carry two independent based torus loops.
Compactness and the quantitative shrink factor rule out such a sequence.

## Quantitative reduction

1. Transfer `K` by the supplied ambient isotopy to the standard product torus.
2. If `distortion K = ∞`, the result is immediate.  Otherwise negate the desired inequality and
   convert it to

   ```lean
   160 * (distortion K).toReal < Nat.min p q.
   ```

3. Start with an oriented box carrying two independent based winding loops.  Smooth the loops,
   select a superellipsoid shell around the box by coarea, and select a transverse cutting level.
   The outer shell contributes at most `76 * distortion K` intersections and each of the two
   regular cut levels contributes at most `40 * distortion K` intersections.
4. Show that the torus part of either the lower or the upper child superellipsoid still carries
   two independent based loops.  Each child lies in a new oriented box of radius at most
   `shrinkFactor` times the old radius.
5. Iterate this shrinking step.  The nested-carrier theorem contradicts the existence of
   independent based loops in boxes whose radii tend to zero.

The constants therefore add as `76 + 40 + 40 = 156`; the benchmark keeps Pardon's convenient
rounded constant `160`.

## Canonical barrier and finite four-port decomposition

For one selected superellipsoid, form the barrier

```text
outer superellipsoid boundary ∪ cutting disk.
```

Its intersection with the transported torus is a finite embedded graph.  Surface regularity,
cut regularity, seam regularity, and compact periodicity give:

- finite outer intersection circles;
- finite cut intersection circles;
- a finite transverse seam set;
- cyclic orders of seam parameters on every active circle;
- exact inward cut excursions and outer lower/upper gaps;
- exact carrier decompositions, including seam-free circle components.

Pair consecutive seam vertices along each cut circle.  Each pair determines one four-port band.
The singular trace in that band consists of two outer arms joined by the cut seam.  The two
regular resolutions are the parallel vertical pairing and the horizontal surgery pairing.

The canonical construction retains all five finite paths:

```text
left vertical, right vertical, bottom horizontal, top horizontal, seam horizontal.
```

Only their compact union is replacement support.  The surrounding ambient-open band is used for
pairwise isolation and for charging every modified point to the counted outer/cut events.

This distinction is essential: an outer intersection circle cannot equal a finite vertical
segment throughout an ambient-open neighborhood, because the circle continues through each port.
Accordingly, all exact carrier equations are stated on compact replacement support, never on the
whole open band.

## Relative planar straightening

Inside the canonical tubular strip, the analytic seam flow produces an embedded five-edge tree:
two full outer arms and the fixed seam segment.  The remaining local topology theorem constructs,
for every band, a plane homeomorphism `H` such that:

1. `H` fixes the seam pointwise;
2. `H` sends the analytic tree to the standard singular `T` carrier;
3. the inverse image under `H` of the compact five-path support meets the literal barrier exactly
   in the analytic tree.

The third condition is one-dimensional.  It is quantified only over the five retained paths,
not over the closed rectangle that they bound.  Thus it is enough to complete the analytic tree
by a lower and an upper connector whose interiors avoid the barrier.  The seam together with the
two completed routes is a theta graph.  The lower and upper connectors map to the standard bottom
and top paths, while the four outer half-arms map to the two standard vertical paths.  Exactness
on those five paths then says precisely that the vertical paths and seam are barrier points and
the two connector interiors are not.

Reparametrizing the tubular strip by `H⁻¹` gives an exact `PairedSeamBandChart`.  Its support is
the image of the compact five-path carrier and lies inside the original disjoint open band.

The construction uses the project-local Moise--Schoenflies infrastructure.  The theta ambient
extension first maps all three theta paths pointwise: the seam, the completed lower route, and the
completed upper route.  Because both completed routes use the same three-piece parametrizations,
this also maps each of the four outer half-arms and both connectors pointwise.  Internally, the
extension fills the two bounded Jordan cells, glues them across the shared seam, and applies an
exterior Alexander extension.

The connector construction must distinguish two existing flows.  The global normalized-height
flow gives a compact collar of the whole inward excursion and changes height by the flow time
throughout the regular coordinate band.  The seam-tangent flow preserves the outer polynomial
and gives the four exact outer arms, but its unit-height law is available only on the outer level;
it cannot soundly be applied to the entire inward excursion.  At time zero, choose one outward
probe immediately before each left crossing and immediately after each right crossing, inside
the local sign-flip neighborhoods.  Their outer defects are positive, while the closed central
subarc between inward probes has strictly negative defect.  These probes are deliberately local:
the larger extension used to obtain the tubular strip can cross unrelated seam points elsewhere
on the same cutting circle.  Uniform continuity and finiteness preserve these signs for all
sufficiently small flow times.  In each endpoint inverse-function chart, the horizontal
height-flow slice then has one unique outer-level crossing.  That crossing is the seam-tangent arm
point at the same height, since both have the prescribed outer polynomial and height and the
local seam chart is injective.  The subpath of the horizontal collar slice between the two
crossings is therefore a connector with the required endpoints.  Its interior has nonzero height
relative to the cut plane and strictly negative outer defect, so it avoids the barrier.  A finite
minimum of the two endpoint-chart radii and the compact central-negativity radius works
simultaneously for all bands.  No corresponding finite-tree ambient-equivalence theorem is
available in pinned Mathlib.

`StandardFourPortTheta` fixes the target parametrization: its lower route is the lower-left half
arm, bottom segment, and lower-right half arm; its upper route is the analogous upper triple.
The source connectors will be concatenated in exactly this order, so the ambient theta map's
three path equations specialize without any additional reparametrization argument.

## Boolean moving-sphere stages

With `n` disjoint bands, index resolutions by Boolean choices `Fin n → Bool`.  Adjacent choices
differ in exactly one band.  For every choice:

- patch an embedded sphere family along the selected compact supports;
- prove its torus intersection is exactly the corresponding resolved graph carrier;
- decompose that intersection into finitely many embedded circles;
- retain inside/outside parity labels;
- charge modified points to the original superellipsoid events.

Order all Boolean choices by a finite Gray-code path.  Consecutive stages are a single quadratic
four-port move.  The explicit six-edge rectangle and coherent-theta analysis show that, when all
intersection circles are inessential, every move is disk-sided in either the current or next
stage.  Forward and reverse disk-sided transitions compose into a finite parity sequence.

At the terminal choice the stage is the separated lower/upper two-sphere rounding.  Hence a
carrying initial cell propagates to a carrying lower or upper child cell.

## Essential-circle branch

If an intermediate sphere has an essential torus-intersection circle, surface topology supplies
a nonzero coordinate-axis winding circle.  Regular continuation transports its transverse
intersection certificate back to the original counted outer/cut barrier.  The event charging map
is injective, so the circle would require at least `Nat.min p q` charged events.  This contradicts
the strict `160 * distortion < Nat.min p q` bound.

Thus either the essential branch immediately contradicts the assumed distortion inequality, or
all stages are inessential and the finite disk-sided parity induction reaches a carrying child.

## Lean assembly

The final implementation path is:

1. `CanonicalEndpointRegularityData` chooses all regular levels and finite cyclic orders.
2. `CanonicalCentralBarrierChartData.ArcExactness` supplies exact compact four-port charts.
3. `SuperellipsoidCanonicalPairedBandWitnessData` constructs the Boolean regular stages,
   charging transports, quadratic side covers, and separated terminal stage.
4. `pardonTarget_of_superellipsoidCanonicalPairedBandAxisWitness` derives the quantitative bound
   for one ambient-isotopy presentation.
5. `Submission.pardon_torus_knot_distortion` unpacks the existential isotopy/reparametrization and
   invokes that theorem.

Completion requires the relative planar straightener, unconditional construction of the Boolean
stage witness, replacement of the remaining `Submission.lean` proof placeholder, a warning-free
full build and comparator run, a trusted-dependency scan showing only the standard three
foundational dependencies, and successful official leaderboard submission.
