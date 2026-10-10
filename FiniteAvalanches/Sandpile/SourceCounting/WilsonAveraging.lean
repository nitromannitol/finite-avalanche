import FiniteAvalanches.Sandpile.SourceCounting.ConditionalAveraging

/-! A generic conditional consumer of the finite source averaging helper. -/
namespace FiniteAvalanches.ConditioningAveragingConsumer
open LatticeProb FiniteAvalanches.Trees FiniteAvalanches.Sandpile MeasureTheory
open FiniteAvalanches.Sandpile.WiredTrees FiniteAvalanches.Sandpile.SourceCounting
open FiniteAvalanches.Sandpile.Components FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.ConditioningConsumer TreeMeasurability11
open scoped Classical
noncomputable section

/-- Internal conditional assembly from a common bound on the actual Wilson
contact reciprocal for each nonsink observation. The forest estimate remains
an explicit premise and is transferred through the exact sealed expectation. -/
theorem source_marks_finiteZN_integral_le_of_wilson_bound {N r : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) (B : ℝ) (hB : 0 ≤ B)
    (hforest : ∀ (t₀ : (graph N).SpanningTree)
      (hne₀ : (graph N).ancestorOf t₀ none (markedVertices (activeMarks N r))
        (marked_vertices_nonempty _ (source_mem_activeMarks N r)) ≠ none),
      (∫ σ, (1 : ℝ) /
        (contacts (activeSites N ((graph N).span t₀ (markedVertices (activeMarks N r))))
          σ : ℝ) ∂wilsonColorLaw
            (observationRootPair N (markedVertices (activeMarks N r))
              (marked_vertices_nonempty _ (source_mem_activeMarks N r)) t₀ hne₀)) ≤ B) :
    (∫ t, finiteZN N (sourceMarks r) (Finset.insert_nonempty _ _) t ∂law N) ≤ B := by
  apply source_marks_finiteZN_integral_le_of_conditional_bound hr hrN B hB
  intro t₀ hne₀
  rw [source_marks_conditional_finiteZN_expectation hr hrN t₀ hne₀]
  exact hforest t₀ hne₀

end
end FiniteAvalanches.ConditioningAveragingConsumer
