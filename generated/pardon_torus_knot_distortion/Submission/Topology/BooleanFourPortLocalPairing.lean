import Submission.Topology.FiniteAlternatingArcCycleDecomposition

/-!
# The Boolean perfect matching on finitely many four-port patches

Each band has left/right and bottom/top port labels.  The false resolution pairs the two levels
on each fixed side; the true resolution pairs the two sides at each fixed level.  This file gives
the resulting perfect matching and combines it with any fixed outside matching.
-/

noncomputable section

namespace Submission.Topology

/-- A port is a band together with its side and level labels. -/
abbrev FourPortVertex (n : ℕ) := Fin n × (Fin 2 × Fin 2)

/-- Each band resolution has two local edges. -/
abbrev FourPortLocalEdge (n : ℕ) := Fin n × Fin 2

/-- The endpoint equivalence of the choice-dependent local four-port matching. -/
def fourPortLocalEndpointEquiv {n : ℕ} (choice : Fin n → Bool) :
    FourPortLocalEdge n × Fin 2 ≃ FourPortVertex n where
  toFun x :=
    if choice x.1.1 = true then
      (x.1.1, (x.2, x.1.2))
    else
      (x.1.1, (x.1.2, x.2))
  invFun v :=
    if choice v.1 = true then
      ((v.1, v.2.2), v.2.1)
    else
      ((v.1, v.2.1), v.2.2)
  left_inv x := by
    rcases x with ⟨⟨b, a⟩, j⟩
    by_cases h : choice b = true <;> simp [h]
  right_inv v := by
    rcases v with ⟨b, s, l⟩
    by_cases h : choice b = true <;> simp [h]

/-- The local perfect matching selected independently in every band. -/
abbrev fourPortLocalPairing {n : ℕ} (choice : Fin n → Bool) :
    FiniteEndpointPairing (FourPortVertex n) where
  edge := FourPortLocalEdge n
  finite_edge := inferInstance
  endpointEquiv := fourPortLocalEndpointEquiv choice

@[simp] theorem fourPortLocalEndpointEquiv_false
    {n : ℕ} {choice : Fin n → Bool} {b : Fin n}
    (hb : choice b = false) (side endpoint : Fin 2) :
    fourPortLocalEndpointEquiv choice ((b, side), endpoint) =
      (b, (side, endpoint)) := by
  simp [fourPortLocalEndpointEquiv, hb]

@[simp] theorem fourPortLocalEndpointEquiv_true
    {n : ℕ} {choice : Fin n → Bool} {b : Fin n}
    (hb : choice b = true) (level endpoint : Fin 2) :
    fourPortLocalEndpointEquiv choice ((b, level), endpoint) =
      (b, (endpoint, level)) := by
  simp [fourPortLocalEndpointEquiv, hb]

/-- A fixed outside matching and a Boolean local matching form a finite degree-two system. -/
def booleanFourPortEndpointSystem {n : ℕ}
    (outside : FiniteEndpointPairing (FourPortVertex n))
    (choice : Fin n → Bool) : FiniteAlternatingEndpointSystem (FourPortVertex n) where
  first := outside
  second := fourPortLocalPairing choice

end Submission.Topology
