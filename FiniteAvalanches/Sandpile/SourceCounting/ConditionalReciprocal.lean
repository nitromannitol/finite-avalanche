import FiniteAvalanches.Trees.Lattice.ConditionalReciprocalExpectation
import FiniteAvalanches.Sandpile.SourceCounting.ConditionalContactLaw
import FiniteAvalanches.Trees.Lattice.TreeContinuityObjects

/-! The reciprocal expectation on the literal six source marks. -/
namespace FiniteAvalanches.ConditioningConsumer
open LatticeProb FiniteAvalanches.Trees FiniteAvalanches.Sandpile MeasureTheory
open FiniteAvalanches.Sandpile.WiredTrees FiniteAvalanches.Sandpile.SourceCounting
open FiniteAvalanches.Sandpile.Components FiniteAvalanches.Wilson.Lattice
open TreeMeasurability11
open scoped Classical
noncomputable section

/-- Resolve the actual marked-vertex preimage and inside-volume branch of the
existing finite normalization. Every one of the six source marks is retained. -/
theorem source_reciprocal_eq_finiteZN {N r : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N)
    (t : (graph N).SpanningTree) :
    reciprocal N (markedVertices (activeMarks N r))
      (marked_vertices_nonempty _ (source_mem_activeMarks N r)) t =
        finiteZN N (sourceMarks r) (Finset.insert_nonempty _ _) t := by
  rw [finiteZN, dif_pos (fun _ hx => sourceMarks_inBox hr hrN hx)]
  have hm : markedVertices (activeMarks N r) = finiteMarks N (sourceMarks r) := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, (Finset.mem_filter.mp hx).2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
  congr 1

/-- The actual source normalization is integrable under the whole copied
observation, with the volume and marks resolved inside the proof. -/
theorem source_marks_conditional_finiteZN_integrable {N r : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) (t₀ : (graph N).SpanningTree) :
    Integrable (finiteZN N (sourceMarks r) (Finset.insert_nonempty _ _))
      (ProbabilityTheory.cond (law N) {t | (graph N).copiedConnectorObservation t₀ t none
        (markedVertices (activeMarks N r))
        (marked_vertices_nonempty _ (source_mem_activeMarks N r))}) := by
  have he : finiteZN N (sourceMarks r) (Finset.insert_nonempty _ _) =
      reciprocal N (markedVertices (activeMarks N r))
        (marked_vertices_nonempty _ (source_mem_activeMarks N r)) := by
    funext t
    exact (source_reciprocal_eq_finiteZN hr hrN t).symm
  rw [he]
  exact integrable_wired_reciprocal _ _ _ _

/-- For `N ≥ r ≥ 2`, the literal finite source reciprocal conditioned on the
whole copied connecting tree and ordered ancestor-to-sink path is exactly the
ordinary Wilson contact-reciprocal integral for the actual observation roots. -/
theorem source_marks_conditional_finiteZN_expectation {N r : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) (t₀ : (graph N).SpanningTree)
    (hne₀ : (graph N).ancestorOf t₀ none (markedVertices (activeMarks N r))
      (marked_vertices_nonempty _ (source_mem_activeMarks N r)) ≠ none) :
    let G := graph N
    let S := markedVertices (activeMarks N r)
    let hS := marked_vertices_nonempty _ (source_mem_activeMarks N r)
    let Ksites := activeSites N (G.span t₀ S)
    let roots := observationRootPair N S hS t₀ hne₀
    (∫ t, finiteZN N (sourceMarks r) (Finset.insert_nonempty _ _)
      t ∂ProbabilityTheory.cond (law N)
        {t | G.copiedConnectorObservation t₀ t none S hS}) =
      ∫ σ, (1 : ℝ) / (contacts Ksites σ : ℝ) ∂wilsonColorLaw roots := by
  dsimp only
  calc
    _ = ∫ t, reciprocal N (markedVertices (activeMarks N r))
        (marked_vertices_nonempty _ (source_mem_activeMarks N r)) t
        ∂ProbabilityTheory.cond (law N) {t | (graph N).copiedConnectorObservation t₀ t none
          (markedVertices (activeMarks N r))
          (marked_vertices_nonempty _ (source_mem_activeMarks N r))} := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => (source_reciprocal_eq_finiteZN hr hrN t).symm)
    _ = _ := finite_whole_observation_conditional_reciprocal_expectation N _ _ t₀ hne₀

end
end FiniteAvalanches.ConditioningConsumer
