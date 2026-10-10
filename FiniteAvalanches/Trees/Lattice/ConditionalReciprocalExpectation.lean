import FiniteAvalanches.Trees.Lattice.FiniteConditionalContactLaw
import FiniteAvalanches.Wilson.Lattice.ReciprocalContactMonotonicity

/-! Transfer of the whole copied-observation contact law to its literal real reciprocal. -/
namespace FiniteAvalanches.ConditioningConsumer
open LatticeProb FiniteAvalanches.Trees FiniteAvalanches.Sandpile MeasureTheory
open FiniteAvalanches.Sandpile.WiredTrees FiniteAvalanches.Wilson.Lattice
open scoped Classical
noncomputable section

/-- The existing source reciprocal is integrable under every finite measure on
the actual copied-tree carrier. -/
theorem integrable_wired_reciprocal (N : ℕ) (S : Set (FiniteWired.Vertex N))
    (hS : S.Nonempty) (μ : Measure (graph N).SpanningTree) [IsFiniteMeasure μ] :
    Integrable (reciprocal N S hS) μ := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
  refine Filter.Eventually.of_forall fun t => ?_
  have hb := (graph N).reciprocalWeight_one_nonneg_le_one none S hS t
  change ‖(graph N).reciprocalWeight none S hS 1 t‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

/-- The whole observation forces the nonsink branch, so the all-count-event law
identifies the pushforward measures of the existing source reciprocal. -/
theorem finite_whole_observation_conditional_reciprocal_law (N : ℕ)
    (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty)
    (t₀ : (graph N).SpanningTree)
    (hne₀ : (graph N).ancestorOf t₀ none S hS ≠ none) :
    (ProbabilityTheory.cond (law N)
      {t | (graph N).copiedConnectorObservation t₀ t none S hS}).map
        (reciprocal N S hS) =
      (wilsonColorLaw (observationRootPair N S hS t₀ hne₀)).map
        (fun σ => (1 : ℝ) / (contacts (activeSites N ((graph N).span t₀ S)) σ : ℝ)) := by
  let G := graph N
  let K := activeSites N (G.span t₀ S)
  let R := observationRootPair N S hS t₀ hne₀
  let P : Set G.SpanningTree := {t | G.copiedConnectorObservation t₀ t none S hS}
  have hm : Measurable (fun σ => (1 : ℝ) / (contacts K σ : ℝ)) :=
    ((continuous_of_discreteTopology : Continuous (fun n : ℕ => (1 : ℝ) / n)).comp
      (continuous_contacts K)).measurable
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply (measurable_of_countable _) hA, Measure.map_apply hm hA]
  have he : ProbabilityTheory.cond (law N) P ((reciprocal N S hS) ⁻¹' A) =
      ProbabilityTheory.cond (law N) P
        {t | ∃ hne : G.ancestorOf t none S hS ≠ none,
          (G.admissibleEdges (G.past t none (G.ancestorOf t none S hS) hne)
            (G.span t S)).card ∈ {n : ℕ | (1 : ℝ) / n ∈ A}} := by
    apply measure_congr
    filter_upwards [ProbabilityTheory.ae_cond_mem (μ := law N)
      (s := P) (Set.toFinite P).measurableSet] with t ht
    have hne : G.ancestorOf t none S hS ≠ none := by
      rw [ht.2.2.1]
      exact hne₀
    have hw (hn : G.ancestorOf t none S hS ≠ none) :
        reciprocal N S hS t = (1 : ℝ) /
          (G.admissibleEdges (G.past t none (G.ancestorOf t none S hS) hn)
            (G.span t S)).card := by
      exact (G.reciprocalWeight_eq_inv_past none S hS t hn).trans (one_div _).symm
    apply propext
    constructor
    · intro htA
      exact ⟨hne, (hw hne) ▸ htA⟩
    · rintro ⟨hn, htA⟩
      change reciprocal N S hS t ∈ A
      rw [hw hn]
      exact htA
  exact he.trans (finite_whole_observation_conditional_contact_law N S hS t₀ hne₀
    {n : ℕ | (1 : ℝ) / n ∈ A})

/-- The conditional expectation of the literal source reciprocal is the
ordinary Wilson integral of the real contact reciprocal, including `1 / 0 = 0`. -/
theorem finite_whole_observation_conditional_reciprocal_expectation (N : ℕ)
    (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty)
    (t₀ : (graph N).SpanningTree)
    (hne₀ : (graph N).ancestorOf t₀ none S hS ≠ none) :
    (∫ t, reciprocal N S hS t ∂ProbabilityTheory.cond (law N)
      {t | (graph N).copiedConnectorObservation t₀ t none S hS}) =
      ∫ σ, (1 : ℝ) / (contacts (activeSites N ((graph N).span t₀ S)) σ : ℝ)
        ∂wilsonColorLaw (observationRootPair N S hS t₀ hne₀) := by
  have hm : Measurable (fun σ => (1 : ℝ) /
      (contacts (activeSites N ((graph N).span t₀ S)) σ : ℝ)) :=
    ((continuous_of_discreteTopology : Continuous (fun n : ℕ => (1 : ℝ) / n)).comp
      (continuous_contacts _)).measurable
  calc
    _ = ∫ x : ℝ, x ∂(ProbabilityTheory.cond (law N)
        {t | (graph N).copiedConnectorObservation t₀ t none S hS}).map
          (reciprocal N S hS) :=
      (integral_map (measurable_of_countable _).aemeasurable
        measurable_id.aestronglyMeasurable).symm
    _ = ∫ x : ℝ, x ∂(wilsonColorLaw (observationRootPair N S hS t₀ hne₀)).map
        (fun σ => (1 : ℝ) / (contacts (activeSites N ((graph N).span t₀ S)) σ : ℝ)) := by
      rw [finite_whole_observation_conditional_reciprocal_law N S hS t₀ hne₀]
    _ = _ := integral_map hm.aemeasurable measurable_id.aestronglyMeasurable

/-- Both functions in the expectation identity are integrable; no integrability
or positivity hypothesis is required from the caller. -/
theorem finite_whole_observation_conditional_reciprocal_integrable (N : ℕ)
    (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty)
    (t₀ : (graph N).SpanningTree)
    (hne₀ : (graph N).ancestorOf t₀ none S hS ≠ none) :
    Integrable (reciprocal N S hS) (ProbabilityTheory.cond (law N)
      {t | (graph N).copiedConnectorObservation t₀ t none S hS}) ∧
      Integrable (fun σ => (1 : ℝ) /
        (contacts (activeSites N ((graph N).span t₀ S)) σ : ℝ))
        (wilsonColorLaw (observationRootPair N S hS t₀ hne₀)) :=
  ⟨integrable_wired_reciprocal N S hS _, integrable_reciprocal_contacts _ _⟩

/-- On the whole observation the descendant count is exactly the nonsink past
count, so its literal real reciprocal has the same ordinary integral. -/
theorem finite_whole_observation_conditional_count_reciprocal (N : ℕ)
    (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty)
    (t₀ : (graph N).SpanningTree)
    (hne₀ : (graph N).ancestorOf t₀ none S hS ≠ none) :
    (∫ t, (1 : ℝ) / ((graph N).admissibleEdges
      ((graph N).descendants t none ((graph N).ancestorOf t none S hS))
      ((graph N).span t S)).card ∂ProbabilityTheory.cond (law N)
        {t | (graph N).copiedConnectorObservation t₀ t none S hS}) =
      ∫ σ, (1 : ℝ) / (contacts (activeSites N ((graph N).span t₀ S)) σ : ℝ)
        ∂wilsonColorLaw (observationRootPair N S hS t₀ hne₀) := by
  calc
    _ = ∫ t, reciprocal N S hS t ∂ProbabilityTheory.cond (law N)
        {t | (graph N).copiedConnectorObservation t₀ t none S hS} := by
      apply integral_congr_ae
      filter_upwards [ProbabilityTheory.ae_cond_mem (μ := law N)
        (s := {t | (graph N).copiedConnectorObservation t₀ t none S hS})
        (Set.toFinite _).measurableSet] with t ht
      have hne : (graph N).ancestorOf t none S hS ≠ none := by
        rw [ht.2.2.1]
        exact hne₀
      exact (if_pos hne).symm
    _ = _ := finite_whole_observation_conditional_reciprocal_expectation N S hS t₀ hne₀

end
end FiniteAvalanches.ConditioningConsumer
