import FiniteAvalanches.Wilson.Lattice.DistantOriginRootPair
import FiniteAvalanches.Wilson.Lattice.WiredJointCylinders

/-! Origin-and-sink stack forests and distant-root wired forest laws. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

/-- The two descriptions of the roots have the same original-copy forests. -/
def distantOriginForestEquiv (B : ℕ) :
    (WiredTrees.graph B).RootedForest (wiredOriginAndSink B) ≃
      FiniteForest (distantOriginRootPair B) B where
  toFun F := ⟨F.val, by rw [wiredRoots_distantOriginRootPair]; exact F.property⟩
  invFun F := ⟨F.val, by rw [← wiredRoots_distantOriginRootPair]; exact F.property⟩
  left_inv F := by apply Subtype.ext; rfl
  right_inv F := by apply Subtype.ext; rfl

/-- The root-set identification preserves ambient lattice edge fields. -/
theorem distantOriginForestEquiv_edgeField (B : ℕ)
    (a : GoodIncidentArrows (WiredTrees.graph B) (wiredOriginAndSink B)) :
    finiteEdgeField (distantOriginRootPair B) B
      (distantOriginForestEquiv B (incidentArrowForest (WiredTrees.graph B) (wiredOriginAndSink B) a)) =
      incidentArrowEdgeField B (wiredOriginAndSink B) a := rfl

/-- Origin-and-sink terminal edge observations have the same probability as
the finite wired forest law for a root placed beyond the box. -/
theorem variableStackLaw_originSinkEdgeEvent_eq_finiteForestLaw (B : ℕ)
    (k : Cursor (FiniteWired.Vertex B)) (E : Finset LatticeEdge) (p : E → Bool) :
    variableStackLaw (IncidentCopy (WiredTrees.graph B))
      (incidentStackEdgeEvent B (wiredOriginAndSink B) k E (fun e => if h : e ∈ E then p ⟨e, h⟩ else false)) =
      finiteForestLaw (distantOriginRootPair B) B
        (jointEvent E ∅ (fun e => if h : e ∈ E then p ⟨e, h⟩ else false) (fun _ => false)) := by
  let R := distantOriginRootPair B
  let q : LatticeEdge → Bool := fun e => if h : e ∈ E then p ⟨e, h⟩ else false
  let S : Set (FiniteForest R B) := wiredObservationCylinder R B E ∅ q (fun _ => false)
  let T : Set ((WiredTrees.graph B).RootedForest (wiredOriginAndSink B)) :=
    (distantOriginForestEquiv B) ⁻¹' S
  have hc : Nat.card T = Nat.card S :=
    Nat.card_preimage_of_injective (distantOriginForestEquiv B).injective
      (by rw [(distantOriginForestEquiv B).surjective.range_eq]; exact Set.subset_univ S)
  have htotal : Fintype.card ((WiredTrees.graph B).RootedForest (wiredOriginAndSink B)) =
      Fintype.card (FiniteForest R B) := Fintype.card_congr (distantOriginForestEquiv B)
  have hm := variableStackLaw_incidentForestEvent_eq (WiredTrees.graph B) (wiredOriginAndSink B) k T
  have hevent : incidentStackEdgeEvent B (wiredOriginAndSink B) k E q =
      {σ | ∃ a : GoodIncidentArrows (WiredTrees.graph B) (wiredOriginAndSink B),
        incidentArrowForest (WiredTrees.graph B) (wiredOriginAndSink B) a ∈ T ∧
        σ ∈ terminalOutputEvent (wiredOriginAndSink B) (incidentCopyHead (WiredTrees.graph B)) k
          (fun v i σ => σ (v, i)) a} := by
    ext σ
    simp only [incidentStackEdgeEvent, Set.mem_setOf_eq]
    constructor
    · rintro ⟨a, ha, hσ⟩
      refine ⟨a, ?_, hσ⟩
      change (∀ e ∈ E, finiteEdgeField R B
        (distantOriginForestEquiv B (incidentArrowForest (WiredTrees.graph B) (wiredOriginAndSink B) a)) e = q e) ∧ _
      exact ⟨ha, by simp⟩
    · rintro ⟨a, ha, hσ⟩
      refine ⟨a, ?_, hσ⟩
      change (∀ e ∈ E, finiteEdgeField R B
        (distantOriginForestEquiv B (incidentArrowForest (WiredTrees.graph B) (wiredOriginAndSink B) a)) e = q e) ∧ _ at ha
      exact ha.1
  change variableStackLaw (IncidentCopy (WiredTrees.graph B))
    (incidentStackEdgeEvent B (wiredOriginAndSink B) k E q) = _
  rw [hevent, hm, finiteForestLaw_jointEvent]
  change (Nat.card T : ℝ≥0∞) / (Fintype.card ((WiredTrees.graph B).RootedForest (wiredOriginAndSink B)) : ℝ≥0∞) =
    FiniteAvalanches.uniformMeasure (FiniteForest R B) S
  rw [FiniteAvalanches.uniformMeasure_apply, hc, htotal]
  simp only [Nat.card_eq_fintype_card]

end
end FiniteAvalanches.Wilson.Lattice
