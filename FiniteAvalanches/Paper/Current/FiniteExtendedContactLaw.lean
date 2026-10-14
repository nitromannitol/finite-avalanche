import FiniteAvalanches.Paper.Current.ConditionalUnorderedContacts

/-! The literal finite contact variable from main.tex:175, including infinity
at a sink ancestor. The nonsink conditional atom is proved to exclude that
branch before applying the actual unordered law at main.tex:269-274. -/
set_option autoImplicit false
namespace FiniteAvalanches.Paper.CurrentDF176
open FiniteAvalanches.ConditioningConsumer
open LatticeProb FiniteAvalanches.Trees FiniteAvalanches.Sandpile MeasureTheory
open FiniteAvalanches.Sandpile.WiredTrees FiniteAvalanches.Sandpile.SourceCounting
open FiniteAvalanches.Sandpile.Components FiniteAvalanches.Wilson.Lattice
open scoped Classical ENNReal
noncomputable section

/-- Every original ambient copy counts once; a sink common ancestor gives infinity. -/
def finiteExtendedContacts (N : ℕ) (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty)
    (t : (graph N).SpanningTree) : ℝ≥0∞ :=
  if hne : (graph N).ancestorOf t none S hS ≠ none then
    ((graph N).admissibleEdges
      ((graph N).past t none ((graph N).ancestorOf t none S hS) hne)
      ((graph N).span t S)).card
  else ⊤

theorem finiteExtendedContacts_of_ne (N : ℕ) (S : Set (FiniteWired.Vertex N))
    (hS : S.Nonempty) (t : (graph N).SpanningTree)
    (hne : (graph N).ancestorOf t none S hS ≠ none) :
    finiteExtendedContacts N S hS t =
      (((graph N).admissibleEdges
        ((graph N).past t none ((graph N).ancestorOf t none S hS) hne)
        ((graph N).span t S)).card : ℝ≥0∞) := by
  rw [finiteExtendedContacts, dif_pos hne]

theorem finiteExtendedContacts_of_sink (N : ℕ) (S : Set (FiniteWired.Vertex N))
    (hS : S.Nonempty) (t : (graph N).SpanningTree)
    (hsink : (graph N).ancestorOf t none S hS = none) :
    finiteExtendedContacts N S hS t = ⊤ := by
  rw [finiteExtendedContacts, dif_neg (not_not.mpr hsink)]

/-- Both prescribed branches determine the source random variable uniquely. -/
theorem finiteExtendedContacts_unique (N : ℕ) (S : Set (FiniteWired.Vertex N))
    (hS : S.Nonempty) (f : (graph N).SpanningTree → ℝ≥0∞)
    (hfinite : ∀ t, ∀ hne : (graph N).ancestorOf t none S hS ≠ none,
      f t = (((graph N).admissibleEdges
        ((graph N).past t none ((graph N).ancestorOf t none S hS) hne)
        ((graph N).span t S)).card : ℝ≥0∞))
    (hinfinite : ∀ t, (graph N).ancestorOf t none S hS = none → f t = ⊤) :
    f = finiteExtendedContacts N S hS := by
  funext t
  by_cases hne : (graph N).ancestorOf t none S hS ≠ none
  · exact (hfinite t hne).trans (finiteExtendedContacts_of_ne N S hS t hne).symm
  · exact (hinfinite t (not_not.mp hne)).trans
      (finiteExtendedContacts_of_sink N S hS t (not_not.mp hne)).symm

/-- Actual source marks, original copied history and the fully extended variable.
The atom's nonsink support is derived from the actual observation in the body. -/
theorem finite_source_extended_unordered_contact_law {N r : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) (t₀ : (graph N).SpanningTree)
    (hne₀ : (graph N).ancestorOf t₀ none (markedVertices (activeMarks N r))
      (marked_vertices_nonempty _ (source_mem_activeMarks N r)) ≠ none) (D : Set ℝ≥0∞) :
    let G := graph N
    let S := markedVertices (activeMarks N r)
    let hS := marked_vertices_nonempty _ (source_mem_activeMarks N r)
    let Ksites := activeSites N (G.span t₀ S)
    let roots := observationRootPair N S hS t₀ hne₀
    ProbabilityTheory.cond (law N)
      {t | G.copiedConnectorObservation t₀ t none S hS}
      {t | finiteExtendedContacts N S hS t ∈ D} =
      wilsonColorLaw roots {σ | unorderedContacts (Ksites : Set (Site 2)) σ ∈ D} := by
  dsimp only
  let S := markedVertices (activeMarks N r)
  let hS := marked_vertices_nonempty _ (source_mem_activeMarks N r)
  let B := {t | (graph N).copiedConnectorObservation t₀ t none S hS}
  let E := {t | ∃ hne : (graph N).ancestorOf t none S hS ≠ none,
    (((graph N).admissibleEdges
      ((graph N).past t none ((graph N).ancestorOf t none S hS) hne)
      ((graph N).span t S)).card : ℝ≥0∞) ∈ D}
  have hm : MeasurableSet B := (Set.toFinite B).measurableSet
  have he : B ∩ {t | finiteExtendedContacts N S hS t ∈ D} = B ∩ E := by
    ext t
    constructor
    · rintro ⟨ht, hc⟩
      have hne : (graph N).ancestorOf t none S hS ≠ none := by
        rw [ht.2.2.1]
        exact hne₀
      change finiteExtendedContacts N S hS t ∈ D at hc
      rw [finiteExtendedContacts_of_ne N S hS t hne] at hc
      exact ⟨ht, hne, hc⟩
    · rintro ⟨ht, hne, hc⟩
      refine ⟨ht, ?_⟩
      change finiteExtendedContacts N S hS t ∈ D
      rwa [finiteExtendedContacts_of_ne N S hS t hne]
  have hcond : ProbabilityTheory.cond (law N) B
      {t | finiteExtendedContacts N S hS t ∈ D} =
      ProbabilityTheory.cond (law N) B E := by
    rw [ProbabilityTheory.cond_apply hm, ProbabilityTheory.cond_apply hm, he]
  exact hcond.trans
    (FiniteAvalanches.Paper.Current.finite_conditional_unordered_contact_law
      hr hrN t₀ hne₀ D).2

end
end FiniteAvalanches.Paper.CurrentDF176

#print axioms FiniteAvalanches.Paper.CurrentDF176.finiteExtendedContacts_of_ne
#print axioms FiniteAvalanches.Paper.CurrentDF176.finiteExtendedContacts_of_sink
#print axioms FiniteAvalanches.Paper.CurrentDF176.finiteExtendedContacts_unique
#print axioms FiniteAvalanches.Paper.CurrentDF176.finite_source_extended_unordered_contact_law
