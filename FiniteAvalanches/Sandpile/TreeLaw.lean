import FiniteAvalanches.Model.WiredTreeExistence
import FiniteAvalanches.Trees.ReciprocalBounds
import FiniteAvalanches.Trees.Positivity

/-! The complete joining count and global reciprocal identity on literal wired tree probability. -/
open scoped Classical ENNReal
open MeasureTheory
namespace FiniteAvalanches.Sandpile.WiredTrees
open FiniteAvalanches.Sandpile

/-- Actual uniform probability on unmarked copied-edge spanning trees of the wired box. -/
noncomputable def law (N : ℕ) : Measure (graph N).SpanningTree := (graph N).treeLaw

instance law_probability (N : ℕ) : IsProbabilityMeasure (law N) :=
  (graph N).treeLaw_probability

/-- Tree count tau_N, with positivity supplied by the explicit row tree. -/
noncomputable def treeCount (N : ℕ) : ℕ := Fintype.card (graph N).SpanningTree

theorem treeCount_pos (N : ℕ) : 0 < treeCount N := Fintype.card_pos

/-- The positive-support range is exactly the positive normalized component-tree product. -/
theorem product_mass_pos_iff (N : ℕ) (C : Set (FiniteWired.Vertex N)) :
    0 < (Fintype.card ((graph N).ComponentTree C) : ℝ) *
      Fintype.card ((graph N).ComponentTree Cᶜ) / treeCount N ↔
      0 < Fintype.card ((graph N).ComponentTree C) ∧
        0 < Fintype.card ((graph N).ComponentTree Cᶜ) :=
  (graph N).tree_product_mass_pos_iff C

noncomputable def reciprocal (N : ℕ) (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty) :
    (graph N).SpanningTree → ℝ := (graph N).reciprocalWeight none S hS 1

/-- Exact event probability, with no assumed tree inhabitance and every sink copy retained. -/
theorem joining_probability (N : ℕ) (C S : Set (FiniteWired.Vertex N))
    (hr : none ∉ C) (hS : S.Nonempty) (hSC : S ⊆ C) (t : (graph N).ComponentTree C) :
    (law N).real {u | (graph N).descendants u none ((graph N).ancestorOf u none S hS) = C ∧
      (graph N).internalEdges C u.val = t.val} =
      (Fintype.card ((graph N).ComponentTree Cᶜ) : ℝ) / treeCount N *
        (∑ v ∈ ((graph N).componentSpan t S hSC).toFinset,
          ((graph N).crossingAt C v).card) :=
  (graph N).treeLaw_real_ancestorPastTree none hr hS t hSC

/-- The past formulation is precisely the manuscript event on its nonroot carrier. -/
theorem joining_probability_past (N : ℕ) (C S : Set (FiniteWired.Vertex N))
    (hr : none ∉ C) (hS : S.Nonempty) (hSC : S ⊆ C) (t : (graph N).ComponentTree C) :
    (law N).real {u | ∃ hne : (graph N).ancestorOf u none S hS ≠ none,
      (graph N).past u none ((graph N).ancestorOf u none S hS) hne = C ∧
        (graph N).internalEdges C u.val = t.val} =
      (Fintype.card ((graph N).ComponentTree Cᶜ) : ℝ) / treeCount N *
        (∑ v ∈ ((graph N).componentSpan t S hSC).toFinset,
          ((graph N).crossingAt C v).card) := by
  have he : {u : (graph N).SpanningTree |
      (graph N).descendants u none ((graph N).ancestorOf u none S hS) = C ∧
        (graph N).internalEdges C u.val = t.val} =
      {u | ∃ hne : (graph N).ancestorOf u none S hS ≠ none,
        (graph N).past u none ((graph N).ancestorOf u none S hS) hne = C ∧
          (graph N).internalEdges C u.val = t.val} := by
    ext u
    simp only [Set.mem_setOf_eq, (graph N).event_iff_past hr hS u, exists_and_right]
  rw [← he]
  exact joining_probability N C S hr hS hSC t

/-- Every ordinary tree has the common mass tau_N^-1. -/
theorem law_singleton (N : ℕ) (u : (graph N).SpanningTree) :
    law N {u} = (treeCount N : ℝ≥0∞)⁻¹ := by
  change ((Nat.card (graph N).SpanningTree : ℝ≥0∞)⁻¹ •
    (Measure.count : Measure (graph N).SpanningTree)) {u} = _
  rw [Measure.smul_apply]
  simp only [smul_eq_mul, Measure.count_singleton, mul_one]
  rw [Nat.card_eq_fintype_card]
  rfl

/-- The global identity uses actual inside-tree probability and the common mass tau_N^-1.
Its product coefficient is a tree count; sandpile shape identification is a separate proof. -/
theorem reciprocal_identity (N : ℕ) (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty) :
    (∫ u, reciprocal N S hS u ∂law N) =
      ∑ C : (graph N).PositiveSupport none S,
        ((Fintype.card ((graph N).ComponentTree C.val) : ℝ) *
          Fintype.card ((graph N).ComponentTree C.valᶜ) / treeCount N) *
            ((graph N).componentLaw C).real ((graph N).insideContact C) :=
  (graph N).integral_reciprocalWeight none S hS

end FiniteAvalanches.Sandpile.WiredTrees
