import FiniteAvalanches.Wilson.Lattice.WiredDualFaceStacks
import FiniteAvalanches.Wilson.Lattice.WiredDualFaceLaw

/-! Wilson cycle popping samples the dual face square's uniform tree law. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

local instance decEqWiredEdgeDualFaceWilsonLaw (B : ℕ) :
    DecidableEq (FiniteWired.Edge B) := Classical.decEq _

/-- The origin face belongs to every dual face square. -/
def wiredDualFaceOrigin (B : ℕ) : WiredDualFace B :=
  wiredDualFaceOfSite B 0 (by intro i; simp)

/-- Origin-rooted cycle popping in the dual face square terminates almost surely. -/
theorem variableStackLaw_ae_wiredDualFaceOrigin_terminates (B : ℕ)
    (k : Cursor (WiredDualFace B)) :
    ∀ᵐ σ ∂variableStackLaw (IncidentCopy (wiredDualFaceGraph B)),
      ∃ l, Relation.ReflTransGen
        (pop_step {wiredDualFaceOrigin B} (incidentCopyHead (wiredDualFaceGraph B))
          (fun v i => σ (v, i))) k l ∧
        terminal {wiredDualFaceOrigin B} (incidentCopyHead (wiredDualFaceGraph B))
          (fun v i => σ (v, i)) l := by
  let T : (wiredDualFaceGraph B).SpanningTree := Classical.choice inferInstance
  let F := (singletonRootedForestEquiv (wiredDualFaceGraph B) (wiredDualFaceOrigin B)).symm T
  let a := forestIncidentArrows (wiredDualFaceGraph B) {wiredDualFaceOrigin B} F
  exact variableStackLaw_ae_terminates _ _ _ _ a

/-- The terminal origin-rooted incident stack has the uniform dual face tree law. -/
theorem variableStackLaw_wiredDualFaceField_event_eq (B : ℕ)
    (k : Cursor (WiredDualFace B)) (A : Set EdgeField) (hA : MeasurableSet A) :
    variableStackLaw (IncidentCopy (wiredDualFaceGraph B))
      {σ | ∃ a : GoodIncidentArrows (wiredDualFaceGraph B) {wiredDualFaceOrigin B},
        wiredDualFaceField (singletonRootedForestEquiv (wiredDualFaceGraph B) (wiredDualFaceOrigin B)
          (incidentArrowForest (wiredDualFaceGraph B) {wiredDualFaceOrigin B} a)) ∈ A ∧
        σ ∈ terminalOutputEvent {wiredDualFaceOrigin B} (incidentCopyHead (wiredDualFaceGraph B)) k
          (fun v i σ => σ (v, i)) a} = wiredDualFaceLaw B A := by
  rw [wiredDualFaceLaw, Measure.map_apply (measurable_of_finite _) hA]
  have h := variableStackLaw_spanningTreeEvent_eq (wiredDualFaceGraph B) (wiredDualFaceOrigin B) k
    {t | wiredDualFaceField t ∈ A}
  change _ = FiniteAvalanches.uniformMeasure (wiredDualFaceGraph B).SpanningTree
    {t | wiredDualFaceField t ∈ A}
  rw [FiniteAvalanches.uniformMeasure_apply]
  simpa only [Nat.card_eq_fintype_card (α := (wiredDualFaceGraph B).SpanningTree), Set.mem_setOf_eq] using h

end
end FiniteAvalanches.Wilson.Lattice
