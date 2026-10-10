import FiniteAvalanches.Trees.JoiningCounts
import FiniteAvalanches.Model.FiniteWired

/-! The exact joining count on the project's literal wired box and exit-copy carrier. -/
open scoped Classical
namespace FiniteAvalanches.Sandpile.WiredTrees
open FiniteAvalanches.Trees
open FiniteAvalanches.Sandpile

/-- Original interior copies and directional exit copies, with the literal sink `none`. -/
noncomputable def graph (N : ℕ) : Multigraph (FiniteWired.Vertex N) (FiniteWired.Edge N) :=
  Multigraph.ofEndpoints FiniteWired.endpoints FiniteWired.endpoints_ne

/-- Exact ordinary-tree cardinal count on the canonical wired endpoint representation. -/
theorem card_ancestorPastTree (N : ℕ) (C S : Set (FiniteWired.Vertex N))
    (hr : none ∉ C) (hS : S.Nonempty) (hSC : S ⊆ C)
    (t : (graph N).ComponentTree C) :
    Fintype.card ((graph N).AncestorPastTree C S none hS t) =
      Fintype.card ((graph N).ComponentTree Cᶜ) *
        ∑ v ∈ ((graph N).componentSpan t S hSC).toFinset,
          ((graph N).crossingAt C v).card := by
  rw [(graph N).card_ancestorPastTree none hr hS t hSC,
    (graph N).card_admissibleEdges C _ ((graph N).componentSpan_subset t S hSC)]

/-- Cancellation uses the common real mass without identifying any sandpile law. -/
theorem reciprocal_ancestorPastTree (N : ℕ) (C S : Set (FiniteWired.Vertex N))
    (hr : none ∉ C) (hS : S.Nonempty) (hSC : S ⊆ C)
    (t : (graph N).ComponentTree C) (c : ℝ) :
    (∑ u : (graph N).AncestorPastTree C S none hS t,
      c / ((graph N).admissibleEdges C ((graph N).span u.val S)).card) =
      if ((graph N).admissibleEdges C ((graph N).componentSpan t S hSC)).Nonempty then
        c * Fintype.card ((graph N).ComponentTree Cᶜ) else 0 :=
  (graph N).reciprocal_ancestorPastTree none hr hS t hSC c

end FiniteAvalanches.Sandpile.WiredTrees
