import Submission.Topology.RegularBandCyclicWinding
import Submission.Topology.ResolvedStageLogicalAdapters
import Submission.Topology.TwoLevelSphereDichotomy

/-!
# Four-cell localization across a regular two-level band

Two disjoint level surfaces give four open cells on the transported torus:
lower, middle, upper, and exterior.  In an all-inessential intersection
system, the canonical maximal-disk complement is connected and carries a
based rank-two pair.  Consequently it lies in one cell.  The incoming parent
carrier excludes the exterior cell, while a cyclic retraction of the regular
middle-band component excludes the middle cell.

The data below contain only the exact cell partition and a subset relation
from the middle cell to a regular-band component.  In particular, failure of
the middle cell to carry rank two is proved, not included as a field.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Topology

noncomputable section

namespace Submission.Topology

open Submission.PardonDistortion Submission.SurfaceRegularValue Submission.Torus

/-- Geometric input for the pure four-cell localization argument.  The
openness, disjointness, exhaustiveness, and parent/exterior relations are the
fields of `cells`; the only new relation is literal containment of the middle
cell in one closed regular-band component. -/
structure RegularBandTwoLevelLocalizationData
    {Phi : AmbientIsotopy} {iota : Type*} [Fintype iota] [DecidableEq iota]
    (S : FiniteSphereSurgeryIntersectionSystem Phi iota)
    {frame : Equiv.Perm (Fin 3)} {d : ℝ}
    (B : OrientedCoordinateRegularBandData Phi frame d) where
  cells : TwoLevelSpherePartition S
  middleBase : transportedTorus Phi
  middleBase_mem : middleBase ∈ B.transportedClosedBand
  middle_subset_component :
    cells.middlePart ⊆ B.closedBandComponent middleBase

namespace RegularBandTwoLevelLocalizationData

variable {Phi : AmbientIsotopy} {iota : Type*} [Fintype iota] [DecidableEq iota]
  {S : FiniteSphereSurgeryIntersectionSystem Phi iota}
  {frame : Equiv.Perm (Fin 3)} {d : ℝ}
  {B : OrientedCoordinateRegularBandData Phi frame d}

/-- A cyclic retraction of the containing regular-band component proves that
the middle cell cannot carry two independent based winding classes. -/
theorem middle_not_carries
    (L : RegularBandTwoLevelLocalizationData S B)
    (D : RegularBandComponentCyclicRetractionData B L.middleBase) :
    ¬ CarriesBasedLoopTorusGenus Phi L.cells.middlePart :=
  not_carriesBasedLoopTorusGenus_mono L.middle_subset_component
    D.not_carriesBasedLoopTorusGenus

/-- Pure two-level localization with one supplied component retraction.

The proof uses the exact open/disjoint/exhaustive four-cell partition to place
the connected canonical core.  It then derives both excluded cases: cyclic
winding excludes the middle, and the incoming parent carrier excludes the
exterior. -/
theorem carries_lower_or_upper
    (L : RegularBandTwoLevelLocalizationData S B)
    (hzero : S.AllInessential)
    (D : RegularBandComponentCyclicRetractionData B L.middleBase)
    (hparent : CarriesBasedLoopTorusGenus Phi L.cells.parentPart) :
    CarriesBasedLoopTorusGenus Phi L.cells.lowerPart ∨
      CarriesBasedLoopTorusGenus Phi L.cells.upperPart := by
  let M := S.canonicalMaximalInessentialTorusDiskFamily hzero
  let P : M.ConnectedPushoutData :=
    MaximalInessentialTorusDiskFamily.canonicalConnectedPushoutData S hzero
  have hcore : CarriesBasedLoopTorusGenus Phi M.diskComplement :=
    carriesBasedLoopTorusGenus_of_finitePuncturePushout P.pushout
  have hconnected : IsConnected M.diskComplement :=
    MaximalInessentialTorusDiskFamily.ConnectedPushoutData.complement_isConnected M P
  rcases L.cells.diskComplement_subset_one_cell M hconnected with
      hlower | hmiddle | hupper | hexterior
  · exact Or.inl (hcore.mono hlower)
  · exact False.elim <| L.middle_not_carries D
      (hcore.mono hmiddle)
  · exact Or.inr (hcore.mono hupper)
  · exact False.elim <|
      L.cells.not_diskComplement_subset_exterior_of_parent_carrier M hparent hexterior

/-- Global cyclic-retraction data supply the component retraction required by
`carries_lower_or_upper`; no noncarrying premise is exposed to callers. -/
theorem carries_lower_or_upper_of_cyclicRetraction
    (L : RegularBandTwoLevelLocalizationData S B)
    (hzero : S.AllInessential)
    (G : OrientedCoordinateRegularBandCyclicRetractionData B)
    (hparent : CarriesBasedLoopTorusGenus Phi L.cells.parentPart) :
    CarriesBasedLoopTorusGenus Phi L.cells.lowerPart ∨
      CarriesBasedLoopTorusGenus Phi L.cells.upperPart := by
  obtain ⟨D⟩ := G.componentRetraction L.middleBase L.middleBase_mem
  exact L.carries_lower_or_upper hzero D hparent

end RegularBandTwoLevelLocalizationData

end Submission.Topology
