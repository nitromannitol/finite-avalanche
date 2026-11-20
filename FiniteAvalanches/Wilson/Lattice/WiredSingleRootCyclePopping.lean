import FiniteAvalanches.Wilson.CyclePopping.SingletonRootTrees
import FiniteAvalanches.Trees.Lattice.WiredLaw

/-! Uniform spanning trees of wired boxes by cycle popping from any root. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

/-- A copied-graph path between distinct vertices supplies an incident copy
at its starting vertex. -/
theorem incidentCopy_nonempty_of_reaches_ne {V E : Type} [Fintype V] [Fintype E]
    (G : Multigraph V E) (F : Finset E) {v w : V} (hvw : v ≠ w)
    (h : G.reaches F v w) : Nonempty (IncidentCopy G v) := by
  rcases h.cases_head with h | ⟨u, hu, _⟩
  · exact (hvw h).elim
  · obtain ⟨e, _, hend⟩ := hu
    exact ⟨⟨e, hend.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)⟩⟩

/-- The active representative of the lattice origin belongs to every wired box. -/
def wiredOrigin (B : ℕ) : FiniteWired.Active B :=
  fun _ => ⟨0, by constructor <;> omega⟩

/-- Every wired-box vertex, including its sink, has an incident original copy. -/
instance wiredIncidentCopyNonempty (B : ℕ) (v : FiniteWired.Vertex B) :
    Nonempty (IncidentCopy (WiredTrees.graph B) v) := by
  let T := WiredTrees.rowTree B
  cases v with
  | none =>
    have h := T.property.2.2.1 none (Set.mem_univ none)
      (some (wiredOrigin B)) (Set.mem_univ _)
    exact incidentCopy_nonempty_of_reaches_ne (WiredTrees.graph B) T.val (by simp) h
  | some v =>
    have h := T.property.2.2.1 (some v) (Set.mem_univ _) none (Set.mem_univ none)
    exact incidentCopy_nonempty_of_reaches_ne (WiredTrees.graph B) T.val (by simp) h

/-- Cycle popping rooted at any wired-box vertex has the ordinary uniform law
on spanning trees of the original copied graph. -/
theorem variableStackLaw_wiredSpanningTreeEvent_eq (B : ℕ) (r : FiniteWired.Vertex B)
    (k : Cursor (FiniteWired.Vertex B)) (S : Set (WiredTrees.graph B).SpanningTree) :
    variableStackLaw (IncidentCopy (WiredTrees.graph B))
      {σ | ∃ a : GoodIncidentArrows (WiredTrees.graph B) {r},
        singletonRootedForestEquiv (WiredTrees.graph B) r
          (incidentArrowForest (WiredTrees.graph B) {r} a) ∈ S ∧
        σ ∈ terminalOutputEvent {r} (incidentCopyHead (WiredTrees.graph B)) k
          (fun v i σ => σ (v, i)) a} = WiredTrees.law B S := by
  rw [variableStackLaw_spanningTreeEvent_eq]
  change (Nat.card S : ℝ≥0∞) / (Fintype.card (WiredTrees.graph B).SpanningTree : ℝ≥0∞) =
    FiniteAvalanches.uniformMeasure (WiredTrees.graph B).SpanningTree S
  simp only [FiniteAvalanches.uniformMeasure_apply, Nat.card_eq_fintype_card]

end
end FiniteAvalanches.Wilson.Lattice
