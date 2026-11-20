import FiniteAvalanches.Wilson.Lattice.WiredDualFaceObservationProbability

/-! Identification of origin-rooted face-stack observations with face tree marginals. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

local instance decEqWiredEdgeDualFaceFiniteLaw (N : ℕ) :
    DecidableEq (FiniteWired.Edge N) := Classical.decEq _

/-- The terminal origin-rooted incident assignment and its face tree have the same edge field. -/
theorem wiredDualFaceIncidentArrowEdgeField_eq_wiredDualFaceField (B : ℕ)
    (a : GoodIncidentArrows (wiredDualFaceGraph (B + 1)) (({wiredDualFaceOrigin (B + 1)} : Set (WiredDualFace (B + 1))))) :
    wiredDualFaceIncidentArrowEdgeField B (({wiredDualFaceOrigin (B + 1)} : Set (WiredDualFace (B + 1)))) a =
      wiredDualFaceField (singletonRootedForestEquiv (wiredDualFaceGraph (B + 1)) (wiredDualFaceOrigin (B + 1))
        (incidentArrowForest (wiredDualFaceGraph (B + 1)) (({wiredDualFaceOrigin (B + 1)} : Set (WiredDualFace (B + 1)))) a)) := rfl

/-- Origin-rooted incident stacks have the finite face-square UST edge-cylinder law. -/
theorem variableStackLaw_wiredDualFaceOriginEdgeEvent_eq_law (B : ℕ)
    (k : Cursor (WiredDualFace (B + 1))) (E : Finset LatticeEdge) (p : E → Bool) :
    variableStackLaw (IncidentCopy (wiredDualFaceGraph (B + 1)))
      (wiredDualFaceIncidentStackEdgeEvent B (({wiredDualFaceOrigin (B + 1)} : Set (WiredDualFace (B + 1)))) k E (fun e => if h : e ∈ E then p ⟨e, h⟩ else false)) =
      wiredDualFaceLaw (B + 1) (cylinder E p) := by
  rw [← variableStackLaw_wiredDualFaceField_event_eq (B + 1) k (cylinder E p) (measurableSet_cylinder E p)]
  congr 1
  ext σ
  simp only [wiredDualFaceIncidentStackEdgeEvent, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, hσ⟩
    refine ⟨a, ?_, hσ⟩
    change E.restrict (wiredDualFaceField (singletonRootedForestEquiv (wiredDualFaceGraph (B + 1))
      (wiredDualFaceOrigin (B + 1)) (incidentArrowForest (wiredDualFaceGraph (B + 1)) (({wiredDualFaceOrigin (B + 1)} : Set (WiredDualFace (B + 1)))) a))) = p
    funext e
    rw [← wiredDualFaceIncidentArrowEdgeField_eq_wiredDualFaceField]
    change wiredDualFaceIncidentArrowEdgeField B (({wiredDualFaceOrigin (B + 1)} : Set (WiredDualFace (B + 1)))) a e.val = p e
    simpa only [dif_pos e.property] using ha e.val e.property
  · rintro ⟨a, ha, hσ⟩
    refine ⟨a, ?_, hσ⟩
    intro e he
    have heq := congrFun ha ⟨e, he⟩
    change wiredDualFaceField (singletonRootedForestEquiv (wiredDualFaceGraph (B + 1))
      (wiredDualFaceOrigin (B + 1)) (incidentArrowForest (wiredDualFaceGraph (B + 1)) (({wiredDualFaceOrigin (B + 1)} : Set (WiredDualFace (B + 1)))) a)) e =
        p ⟨e, he⟩ at heq
    rw [← wiredDualFaceIncidentArrowEdgeField_eq_wiredDualFaceField] at heq
    simpa only [dif_pos he] using heq

end
end FiniteAvalanches.Wilson.Lattice
