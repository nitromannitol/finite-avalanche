import FiniteAvalanches.Paper.Revision0F522C0.FiniteConditionalStatement
import FiniteAvalanches.Wilson.Lattice.UnorderedContacts

/-! Current cd552a rd:conditional-law with the literal unordered lattice count.
The complete original copied connector and ordered strict tail remain the
conditioning datum. Its positive atom and finite count dictionary are proved. -/
set_option autoImplicit false
namespace FiniteAvalanches.Paper.Current
open FiniteAvalanches.ConditioningConsumer
open LatticeProb FiniteAvalanches.Trees FiniteAvalanches.Sandpile MeasureTheory
open FiniteAvalanches.Sandpile.WiredTrees FiniteAvalanches.Sandpile.SourceCounting
open FiniteAvalanches.Sandpile.Components FiniteAvalanches.Wilson.Lattice
open scoped Classical ENNReal
noncomputable section

/-- The color-law projection retains the source colors at every original root. -/
theorem wilsonColorLaw_ae_root_colors (R : RootPair) :
    ∀ᵐ σ ∂wilsonColorLaw R,
      (∀ x ∈ R.one, σ x = true) ∧ ∀ x ∈ R.zero, σ x = false := by
  rw [wilsonColorLaw, ae_map_iff measurable_snd.aemeasurable]
  · exact wilsonLaw_ae_root_colors R
  · apply MeasurableSet.inter
    · have h := MeasurableSet.iInter (fun x : Site 2 =>
        MeasurableSet.iInter (fun (_ : x ∈ R.one) =>
          (measurable_pi_apply x : Measurable (fun σ : ColorField => σ x))
            (measurableSet_singleton true)))
      convert h using 1
      ext σ
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
      rfl
    · have h := MeasurableSet.iInter (fun x : Site 2 =>
        MeasurableSet.iInter (fun (_ : x ∈ R.zero) =>
          (measurable_pi_apply x : Measurable (fun σ : ColorField => σ x))
            (measurableSet_singleton false)))
      convert h using 1
      ext σ
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
      rfl

/-- Zero connector roots make the original incidence statistic an unordered count almost surely. -/
theorem ae_unorderedContacts_eq_contacts (R : RootPair) (K : Finset (Site 2))
    (hK : (K : Set (Site 2)) ⊆ R.zero) :
    ∀ᵐ σ ∂wilsonColorLaw R,
      unorderedContacts (K : Set (Site 2)) σ = (contacts K σ : ℝ≥0∞) := by
  filter_upwards [wilsonColorLaw_ae_root_colors R] with σ hσ
  exact unorderedContacts_eq_contacts K σ (fun x hx => hσ.2 x (hK hx))

/-- Exact current finite conditional law with all original unordered contacts and the strict tail. -/
theorem finite_conditional_unordered_contact_law {N r : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) (t₀ : (graph N).SpanningTree)
    (hne₀ : (graph N).ancestorOf t₀ none (markedVertices (activeMarks N r))
      (marked_vertices_nonempty _ (source_mem_activeMarks N r)) ≠ none) (D : Set ℝ≥0∞) :
    let G := graph N
    let S := markedVertices (activeMarks N r)
    let hS := marked_vertices_nonempty _ (source_mem_activeMarks N r)
    let Ksites := activeSites N (G.span t₀ S)
    let roots := observationRootPair N S hS t₀ hne₀
    Disjoint (Ksites : Set (Site 2))
      ({x | ¬FiniteWired.inBox N x} ∪
        {x | FiniteWired.inBox N x ∧ wiredSite N x ∈ G.orderedAncestorTail t₀ none S hS}) ∧
    ProbabilityTheory.cond (law N)
      {t | G.copiedConnectorObservation t₀ t none S hS}
      {t | ∃ hne : G.ancestorOf t none S hS ≠ none,
        (((G.admissibleEdges (G.past t none (G.ancestorOf t none S hS) hne)
          (G.span t S)).card : ℕ) : ℝ≥0∞) ∈ D} =
      wilsonColorLaw roots {σ | unorderedContacts (Ksites : Set (Site 2)) σ ∈ D} := by
  dsimp only
  obtain ⟨hd, hlaw⟩ :=
    FiniteAvalanches.Paper.Revision0F522C0.finite_conditional_contact_count_law hr hrN t₀ hne₀
      {n : ℕ | (n : ℝ≥0∞) ∈ D}
  refine ⟨hd, hlaw.trans ?_⟩
  apply measure_congr
  filter_upwards [ae_unorderedContacts_eq_contacts
    (observationRootPair N _ _ t₀ hne₀) (activeSites N ((graph N).span t₀ _))
    (by rw [observationRootPair_zero_eq_activeSites])] with σ hσ
  apply propext
  change (contacts _ σ : ℝ≥0∞) ∈ D ↔ unorderedContacts _ σ ∈ D
  rw [hσ]

/-- A probability-one root dictionary also gives equality of the full count pushforward laws. -/
theorem unordered_contact_count_law_eq (R : RootPair) (K : Finset (Site 2))
    (hK : (K : Set (Site 2)) ⊆ R.zero) :
    (wilsonColorLaw R).map (unorderedContacts (K : Set (Site 2))) =
      (wilsonColorLaw R).map (fun σ => (contacts K σ : ℝ≥0∞)) := by
  exact Measure.map_congr (ae_unorderedContacts_eq_contacts R K hK)

end
end FiniteAvalanches.Paper.Current
