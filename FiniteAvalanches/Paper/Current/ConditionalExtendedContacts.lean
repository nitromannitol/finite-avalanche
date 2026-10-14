import FiniteAvalanches.Paper.Current.FiniteExtendedContactLaw

/-! Avoidance and the conditional law of the complete finite contact count,
given the original copied connecting subtree and its strict rootward tail. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Paper.Current
open FiniteAvalanches.ConditioningConsumer
open LatticeProb FiniteAvalanches.Trees FiniteAvalanches.Sandpile MeasureTheory
open FiniteAvalanches.Sandpile.WiredTrees FiniteAvalanches.Sandpile.SourceCounting
open FiniteAvalanches.Sandpile.Components FiniteAvalanches.Wilson.Lattice
open scoped Classical ENNReal
noncomputable section

/-- The strict ancestor tail and the whole exterior avoid the marked subtree,
and the complete extended contact variable has its two-root unordered law. -/
theorem finite_conditional_extended_contact_law {N r : ℕ}
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
      {t | CurrentDF176.finiteExtendedContacts N S hS t ∈ D} =
      wilsonColorLaw roots {σ | unorderedContacts (Ksites : Set (Site 2)) σ ∈ D} := by
  exact ⟨(finite_conditional_unordered_contact_law hr hrN t₀ hne₀ D).1,
    CurrentDF176.finite_source_extended_unordered_contact_law hr hrN t₀ hne₀ D⟩

end
end FiniteAvalanches.Paper.Current
