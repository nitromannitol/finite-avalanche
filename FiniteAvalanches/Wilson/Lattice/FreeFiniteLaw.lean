import FiniteAvalanches.Wilson.Lattice.FreeObservationProbability

/-! Identification of origin-rooted free-stack observations with free tree marginals. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

local instance decEqInteriorEdgeFreeFiniteLaw (N : ℕ) :
    DecidableEq (FiniteWired.InteriorEdge N) := Classical.decEq _

/-- The terminal origin-rooted incident assignment and its free tree have the same edge field. -/
theorem freeIncidentArrowEdgeField_eq_freeBoxField (B : ℕ)
    (a : GoodIncidentArrows (freeBoxGraph (B + 1)) (freeOriginRoot B)) :
    freeIncidentArrowEdgeField B (freeOriginRoot B) a =
      freeBoxField (singletonRootedForestEquiv (freeBoxGraph (B + 1)) (wiredOrigin (B + 1))
        (incidentArrowForest (freeBoxGraph (B + 1)) (freeOriginRoot B) a)) := rfl

/-- Origin-rooted incident stacks have the finite free UST edge-cylinder law. -/
theorem variableStackLaw_freeOriginEdgeEvent_eq_freeBoxLaw (B : ℕ)
    (k : Cursor (FiniteWired.Active (B + 1))) (E : Finset LatticeEdge) (p : E → Bool) :
    variableStackLaw (IncidentCopy (freeBoxGraph (B + 1)))
      (freeIncidentStackEdgeEvent B (freeOriginRoot B) k E (fun e => if h : e ∈ E then p ⟨e, h⟩ else false)) =
      freeBoxLaw B (cylinder E p) := by
  rw [← variableStackLaw_freeBoxField_event_eq B k (cylinder E p) (measurableSet_cylinder E p)]
  congr 1
  ext σ
  simp only [freeIncidentStackEdgeEvent, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, hσ⟩
    refine ⟨a, ?_, hσ⟩
    change E.restrict (freeBoxField (singletonRootedForestEquiv (freeBoxGraph (B + 1))
      (wiredOrigin (B + 1)) (incidentArrowForest (freeBoxGraph (B + 1)) (freeOriginRoot B) a))) = p
    funext e
    rw [← freeIncidentArrowEdgeField_eq_freeBoxField]
    change freeIncidentArrowEdgeField B (freeOriginRoot B) a e.val = p e
    simpa only [dif_pos e.property] using ha e.val e.property
  · rintro ⟨a, ha, hσ⟩
    refine ⟨a, ?_, hσ⟩
    intro e he
    have heq := congrFun ha ⟨e, he⟩
    change freeBoxField (singletonRootedForestEquiv (freeBoxGraph (B + 1))
      (wiredOrigin (B + 1)) (incidentArrowForest (freeBoxGraph (B + 1)) (freeOriginRoot B) a)) e =
        p ⟨e, he⟩ at heq
    rw [← freeIncidentArrowEdgeField_eq_freeBoxField] at heq
    simpa only [dif_pos he] using heq

end
end FiniteAvalanches.Wilson.Lattice
