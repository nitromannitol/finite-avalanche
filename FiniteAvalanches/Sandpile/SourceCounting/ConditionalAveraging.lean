import FiniteAvalanches.MeasureTheory.FinitePartitionAveraging
import FiniteAvalanches.Sandpile.SourceCounting.ConditionalReciprocal
import FiniteAvalanches.Trees.Lattice.ReciprocalExpectationLimit

/-! Internal conditional assembly of the finite source reciprocal expectation. -/
namespace FiniteAvalanches.ConditioningConsumer
open LatticeProb FiniteAvalanches.Trees FiniteAvalanches.Sandpile MeasureTheory
open FiniteAvalanches.Sandpile.WiredTrees FiniteAvalanches.Sandpile.SourceCounting
open FiniteAvalanches.Sandpile.Components TreeMeasurability11
open scoped Classical
noncomputable section

/-- Literal equality of all five observation fields is an equivalence relation,
including the original branch and outgoing copies and the ordered strict tail. -/
theorem copiedConnectorObservation_equivalence {V E : Type} [Fintype V] [Fintype E]
    (G : Multigraph V E) (root : V) (S : Set V) (hS : S.Nonempty) :
    Equivalence (fun t₀ t : G.SpanningTree => G.copiedConnectorObservation t₀ t root S hS) := by
  refine ⟨fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
  · intro t₀ t h
    exact ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.symm⟩
  · intro t₀ t t' h h'
    exact ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1,
      h'.2.2.2.1.trans h.2.2.2.1, h'.2.2.2.2.trans h.2.2.2.2⟩

/-- Conditional internal averaging: a single nonnegative bound on the ordinary
conditional expectation at every actual nonsink whole observation bounds the
unconditional finite source expectation. The conditional estimate is an explicit
input to this helper; sink atoms, integrability and partition facts are derived. -/
theorem source_marks_finiteZN_integral_le_of_conditional_bound {N r : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ t₀ : (graph N).SpanningTree,
      (graph N).ancestorOf t₀ none (markedVertices (activeMarks N r))
        (marked_vertices_nonempty _ (source_mem_activeMarks N r)) ≠ none →
      (∫ t, finiteZN N (sourceMarks r) (Finset.insert_nonempty _ _) t
        ∂ProbabilityTheory.cond (law N)
          {t | (graph N).copiedConnectorObservation t₀ t none
            (markedVertices (activeMarks N r))
            (marked_vertices_nonempty _ (source_mem_activeMarks N r))}) ≤ B) :
    (∫ t, finiteZN N (sourceMarks r) (Finset.insert_nonempty _ _) t ∂law N) ≤ B := by
  let S := markedVertices (activeMarks N r)
  let hS : S.Nonempty := marked_vertices_nonempty _ (source_mem_activeMarks N r)
  let f := finiteZN N (sourceMarks r) (Finset.insert_nonempty _ _)
  let obs : Setoid (graph N).SpanningTree :=
    ⟨fun t₀ t => (graph N).copiedConnectorObservation t₀ t none S hS,
      copiedConnectorObservation_equivalence (graph N) none S hS⟩
  have hf : Integrable f (law N) := by
    apply (integrable_const (1 : ℝ)).mono'
      (measurable_of_countable f).aestronglyMeasurable
    refine Filter.Eventually.of_forall fun t => ?_
    have hb := ReciprocalLimit15.finiteZN_bounds N (sourceMarks r)
      (Finset.insert_nonempty _ _) t
    change ‖finiteZN N (sourceMarks r) (Finset.insert_nonempty _ _) t‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2
  have hzero (t : (graph N).SpanningTree)
      (hsink : (graph N).ancestorOf t none S hS = none) : f t = 0 := by
    change finiteZN N (sourceMarks r) (Finset.insert_nonempty _ _) t = 0
    rw [← source_reciprocal_eq_finiteZN hr hrN t]
    exact (graph N).reciprocalWeight_eq_zero_of_ancestor_eq_root none S hS t hsink
  apply integral_le_of_finite_equivalence_cond_bound (law N) obs f hf B
  · intro t₀
    exact (finite_whole_observation_pos N S hS t₀).ne'
  · intro t₀
    by_cases hne : (graph N).ancestorOf t₀ none S hS ≠ none
    · exact hbound t₀ hne
    · have hsink : (graph N).ancestorOf t₀ none S hS = none := not_ne_iff.mp hne
      have hz : (∫ t, f t ∂ProbabilityTheory.cond (law N)
          {t | obs.r t₀ t}) = 0 := by
        calc
          _ = ∫ _ : (graph N).SpanningTree, (0 : ℝ)
              ∂ProbabilityTheory.cond (law N) {t | obs.r t₀ t} := by
            apply integral_congr_ae
            filter_upwards [ProbabilityTheory.ae_cond_mem (μ := law N)
              (s := {t | obs.r t₀ t}) (Set.toFinite _).measurableSet] with t ht
            exact hzero t (ht.2.2.1.trans hsink)
          _ = 0 := integral_zero _ _
      exact hz ▸ hB

end
end FiniteAvalanches.ConditioningConsumer
