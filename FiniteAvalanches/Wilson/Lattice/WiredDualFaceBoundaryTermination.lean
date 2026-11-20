import FiniteAvalanches.Wilson.Lattice.WiredDualFaceWilsonLaw
import FiniteAvalanches.Wilson.Lattice.WiredDualFaceHistoryLimit

/-! Termination of face-square cycle popping with additional boundary roots. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

local instance decEqWiredEdgeDualFaceBoundaryTermination (B : ℕ) :
    DecidableEq (FiniteWired.Edge B) := Classical.decEq _

/-- The origin face belongs to the origin-and-boundary root set. -/
theorem wiredDualFaceOrigin_subset_originAndBoundary (B : ℕ) :
    ({wiredDualFaceOrigin (B + 1)} : Set (WiredDualFace (B + 1))) ⊆
      wiredDualFaceOriginAndBoundary B := by
  intro v hv
  have hv' : v = wiredDualFaceOrigin (B + 1) := Set.mem_singleton_iff.mp hv
  subst v
  left
  rfl

/-- Origin-and-boundary cycle popping in the face square terminates almost surely. -/
theorem variableStackLaw_ae_wiredDualFaceOriginAndBoundary_terminates (B : ℕ)
    (k : Cursor (WiredDualFace (B + 1))) :
    ∀ᵐ σ ∂variableStackLaw (IncidentCopy (wiredDualFaceGraph (B + 1))),
      ∃ l, Relation.ReflTransGen
        (pop_step (wiredDualFaceOriginAndBoundary B)
          (incidentCopyHead (wiredDualFaceGraph (B + 1))) (fun v i => σ (v, i))) k l ∧
        terminal (wiredDualFaceOriginAndBoundary B)
          (incidentCopyHead (wiredDualFaceGraph (B + 1))) (fun v i => σ (v, i)) l := by
  let T : (wiredDualFaceGraph (B + 1)).SpanningTree := Classical.choice inferInstance
  let F := (singletonRootedForestEquiv (wiredDualFaceGraph (B + 1))
    (wiredDualFaceOrigin (B + 1))).symm T
  let a := forestIncidentArrows (wiredDualFaceGraph (B + 1)) {wiredDualFaceOrigin (B + 1)} F
  have ha : GoodIncidentArrows (wiredDualFaceGraph (B + 1)) (wiredDualFaceOriginAndBoundary B) :=
    ⟨a.val, terminal_mono_roots {wiredDualFaceOrigin (B + 1)} (wiredDualFaceOriginAndBoundary B)
      (incidentCopyHead (wiredDualFaceGraph (B + 1))) (fun v _ => a.val v) 0
      (wiredDualFaceOrigin_subset_originAndBoundary B) a.property⟩
  exact variableStackLaw_ae_terminates _ _ _ _ ha

end
end FiniteAvalanches.Wilson.Lattice
