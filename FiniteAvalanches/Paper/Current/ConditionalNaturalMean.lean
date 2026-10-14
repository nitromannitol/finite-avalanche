import FiniteAvalanches.Paper.Current.ConditionalContactMean

namespace CountDictionaryReview
open LatticeProb MeasureTheory FiniteAvalanches FiniteAvalanches.Trees FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.WiredTrees FiniteAvalanches.Sandpile.SourceCounting
open FiniteAvalanches.Sandpile.Components FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.ConditioningConsumer TreeMeasurability11.CurrentDomain
open scoped Classical ENNReal
noncomputable section

/-- The actual Main consumer derives the zero-root dictionary before using the real natural reciprocal. -/
theorem actual_guarded_conditional_natural_mean {N r : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) (t₀ : (graph N).SpanningTree)
    (hne₀ : (graph N).ancestorOf t₀ none (markedVertices (activeMarks N r))
      (marked_vertices_nonempty _ (source_mem_activeMarks N r)) ≠ none) :
    let S := markedVertices (activeMarks N r)
    let hS := marked_vertices_nonempty _ (source_mem_activeMarks N r)
    let K := activeSites N ((graph N).span t₀ S)
    let R := observationRootPair N S hS t₀ hne₀
    (∫ t, sourceFiniteReciprocal N (sourceMarks r) (Finset.insert_nonempty _ _)
      (fun _ hx => sourceMarks_inBox hr hrN hx) t
      ∂ProbabilityTheory.cond (law N)
        {t | (graph N).copiedConnectorObservation t₀ t none S hS}) =
      ∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw R := by
  have h := actual_conditional_guarded_mean hr hrN t₀ hne₀
  dsimp only at h ⊢
  refine h.trans ?_
  apply integral_congr_ae
  filter_upwards [Paper.Current.ae_unorderedContacts_eq_contacts
    (observationRootPair N _ _ t₀ hne₀) (activeSites N ((graph N).span t₀ _))
    (by rw [observationRootPair_zero_eq_activeSites])] with σ hσ
  rw [hσ, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]

/-- The endpoint N=r consumes the same actual observation, without a lost mark. -/
theorem actual_guarded_conditional_natural_mean_endpoint (r : ℕ) (hr : 2 ≤ r)
    (t₀ : (graph r).SpanningTree)
    (hne₀ : (graph r).ancestorOf t₀ none (markedVertices (activeMarks r r))
      (marked_vertices_nonempty _ (source_mem_activeMarks r r)) ≠ none) :
    let S := markedVertices (activeMarks r r)
    let hS := marked_vertices_nonempty _ (source_mem_activeMarks r r)
    let K := activeSites r ((graph r).span t₀ S)
    let R := observationRootPair r S hS t₀ hne₀
    (∫ t, sourceFiniteReciprocal r (sourceMarks r) (Finset.insert_nonempty _ _)
      (fun _ hx => sourceMarks_inBox hr le_rfl hx) t
      ∂ProbabilityTheory.cond (law r)
        {t | (graph r).copiedConnectorObservation t₀ t none S hS}) =
      ∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw R :=
  actual_guarded_conditional_natural_mean hr le_rfl t₀ hne₀

end
end CountDictionaryReview

#print axioms CountDictionaryReview.actual_guarded_conditional_natural_mean
#print axioms CountDictionaryReview.actual_guarded_conditional_natural_mean_endpoint
