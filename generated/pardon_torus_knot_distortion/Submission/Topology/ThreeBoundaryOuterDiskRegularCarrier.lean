import Submission.Topology.ThreeBoundaryCanonicalDiskSides

/-!
# The exterior complement of a regular three-boundary carrier

This module isolates the elementary codimension-zero input needed for the exterior-complement
field of `ThreeBoundaryPairOfPantsTopology`.  No compact-surface classification is used.  When
the carrier is closed and its named interior is open, the carrier cuts out a clopen subset of
the simultaneous canonical-disk complement.  Existing finite radial pushout connectivity then
forces that clopen subset to be the whole complement.

The independent pair-of-pants boundary-generation statement is deliberately not included here.
That statement requires a genuine pair-of-pants fundamental-group or first-homology theorem,
which is not supplied by the current surface-classification API.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.Torus

variable {Phi : AmbientIsotopy}

/-- The two ordinary regular-closed facts about a codimension-zero compact carrier. -/
structure ThreeBoundaryRegularClosedCarrierData
    (Q : ThreeBoundaryPairOfPantsCarrier Phi) where
  interior_isOpen : IsOpen Q.interior
  carrier_isClosed : IsClosed Q.carrier

namespace ThreeBoundaryRegularClosedCarrierData

variable {Q : ThreeBoundaryPairOfPantsCarrier Phi}

/-- Pairwise-disjoint canonical disks have connected simultaneous complement. -/
theorem diskComplement_isConnected
    (hdisjoint : Pairwise fun i j ↦ Disjoint (Q.disk i) (Q.disk j)) :
    IsConnected Q.diskComplement := by
  let D := Classical.choice <|
    EmbeddedTorusIntersectionCircle.exists_separatedZeroWindingDiskSupports_of_pairwise_disjoint
      Q.circle Q.zeroWinding hdisjoint
  change IsConnected
    (EmbeddedTorusIntersectionCircle.finiteZeroWindingDiskComplement Q.circle Q.zeroWinding)
  rw [← D.range_finitePush, ← Set.image_univ]
  exact (transportedFinitePointComplement_isConnected
      (EmbeddedTorusIntersectionCircle.finiteZeroWindingDiskCenters
        Q.circle Q.zeroWinding)).image D.finitePush
    (D.toFiniteSupportedDiskReplacements.toFiniteSequentialPunctureStages.continuous_push
      |>.continuousOn)

/-- If the carrier is on the exterior side of all three disks, its open interior is contained in
the simultaneous disk complement. -/
theorem interior_subset_diskComplement
    (hexterior : ∀ i, Disjoint Q.carrier (Q.disk i \ Q.boundary i)) :
    Q.interior ⊆ Q.diskComplement := by
  intro x hx i hxdisk
  have hxCarrier : x ∈ Q.carrier := Q.interior_subset_carrier hx
  have hxNotBoundary : x ∉ Q.boundary i := by
    intro hxBoundary
    have hxCarrierBoundary : x ∈ Q.carrier \ Q.interior := by
      rw [Q.boundary_exact]
      exact Set.mem_iUnion.mpr ⟨i, hxBoundary⟩
    exact hxCarrierBoundary.2 hx
  exact Set.disjoint_left.mp (hexterior i) hxCarrier ⟨hxdisk, hxNotBoundary⟩

/-- The regular-closed carrier facts supply the global all-exterior complement inclusion used
by `ThreeBoundaryPairOfPantsTopology`. -/
theorem exterior_complement_subset
    (R : ThreeBoundaryRegularClosedCarrierData Q)
    (hexterior : ∀ i, Disjoint Q.carrier (Q.disk i \ Q.boundary i)) :
    Q.diskComplement ⊆ Q.carrier := by
  have hdisjoint := Q.disks_pairwise_disjoint_of_all_exterior hexterior
  have hconnected : IsConnected Q.diskComplement := diskComplement_isConnected hdisjoint
  have hinterior : Q.interior ⊆ Q.diskComplement := interior_subset_diskComplement hexterior
  let carrierInComplement : Set Q.diskComplement :=
    Subtype.val ⁻¹' Q.carrier
  have hcarrierEqInterior : carrierInComplement = Subtype.val ⁻¹' Q.interior := by
    ext x
    constructor
    · intro hxCarrier
      by_contra hxInterior
      have hxBoundary : x.1 ∈ Q.carrier \ Q.interior := ⟨hxCarrier, hxInterior⟩
      rw [Q.boundary_exact] at hxBoundary
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxBoundary
      exact x.2 i (Q.boundary_subset_disk i hxi)
    · intro hxInterior
      exact Q.interior_subset_carrier hxInterior
  have hclopen : IsClopen carrierInComplement := by
    constructor
    · exact R.carrier_isClosed.preimage continuous_subtype_val
    · rw [hcarrierEqInterior]
      exact R.interior_isOpen.preimage continuous_subtype_val
  let _ : ConnectedSpace Q.diskComplement :=
    isConnected_iff_connectedSpace.mp hconnected
  have hnonempty : carrierInComplement.Nonempty := by
    obtain ⟨x, hx⟩ := Q.interior_nonempty
    exact ⟨⟨x, hinterior hx⟩, Q.interior_subset_carrier hx⟩
  have hall : carrierInComplement = Set.univ := hclopen.eq_univ hnonempty
  intro x hx
  have hxCarrier : (⟨x, hx⟩ : Q.diskComplement) ∈ carrierInComplement := by
    rw [hall]
    exact Set.mem_univ _
  exact hxCarrier

/-- The projected Jordan-side API derives the local canonical-side alternative, so the only
remaining global premise in this constructor is boundary generation of winding. -/
theorem toThreeBoundaryPairOfPantsTopology
    (R : ThreeBoundaryRegularClosedCarrierData Q)
    (hgenerated : ∀ L : TransportedWindingLoop Phi Q.carrier,
      ∃ a : Fin 3 → ℤ,
        L.windingPair = ∑ i, a i • (Q.circle i).windingLoop.windingPair) :
    ThreeBoundaryPairOfPantsTopology Q where
  canonicalInteriorDiskSides := Q.hasCanonicalInteriorDiskSides
  exterior_complement_subset := R.exterior_complement_subset
  winding_generated_by_boundary := hgenerated

end ThreeBoundaryRegularClosedCarrierData

end Submission.Topology
