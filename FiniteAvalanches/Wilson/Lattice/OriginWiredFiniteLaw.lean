import FiniteAvalanches.Wilson.Lattice.OriginWiredObservationProbability

/-! Identification of origin-rooted stack observations with wired UST marginals. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- A terminal incident assignment and its associated singleton-rooted tree
have identical ambient edge fields. -/
theorem incidentArrowEdgeField_eq_wiredField (B : ℕ)
    (a : GoodIncidentArrows (WiredTrees.graph B) (wiredOriginRoot B)) :
    incidentArrowEdgeField B (wiredOriginRoot B) a =
      wiredField (singletonRootedForestEquiv (WiredTrees.graph B) (some (wiredOrigin B))
        (incidentArrowForest (WiredTrees.graph B) (wiredOriginRoot B) a)) := rfl

/-- Origin-rooted incident stacks have exactly the finite wired UST edge
cylinder probabilities. -/
theorem variableStackLaw_originEdgeEvent_eq_finiteLaw (B : ℕ)
    (k : Cursor (FiniteWired.Vertex B)) (E : Finset LatticeEdge) (p : E → Bool) :
    variableStackLaw (IncidentCopy (WiredTrees.graph B))
      (incidentStackEdgeEvent B (wiredOriginRoot B) k E (fun e => if h : e ∈ E then p ⟨e, h⟩ else false)) =
      finiteLaw B (cylinder E p) := by
  rw [finiteLaw_apply B (cylinder E p) (measurableSet_cylinder E p)]
  rw [← variableStackLaw_wiredSpanningTreeEvent_eq B (some (wiredOrigin B)) k
    {t | wiredField t ∈ cylinder E p}]
  congr 1
  ext σ
  simp only [incidentStackEdgeEvent, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, hσ⟩
    refine ⟨a, ?_, hσ⟩
    change E.restrict (wiredField (singletonRootedForestEquiv (WiredTrees.graph B)
      (some (wiredOrigin B)) (incidentArrowForest (WiredTrees.graph B) (wiredOriginRoot B) a))) = p
    funext e
    rw [← incidentArrowEdgeField_eq_wiredField]
    change incidentArrowEdgeField B (wiredOriginRoot B) a e.val = p e
    simpa only [dif_pos e.property] using ha e.val e.property
  · rintro ⟨a, ha, hσ⟩
    refine ⟨a, ?_, hσ⟩
    intro e he
    have heq := congrFun ha ⟨e, he⟩
    change wiredField (singletonRootedForestEquiv (WiredTrees.graph B)
      (some (wiredOrigin B)) (incidentArrowForest (WiredTrees.graph B) (wiredOriginRoot B) a)) e =
        p ⟨e, he⟩ at heq
    rw [← incidentArrowEdgeField_eq_wiredField] at heq
    simpa only [dif_pos he] using heq

end
end FiniteAvalanches.Wilson.Lattice
