import FiniteAvalanches.Sandpile.Components.CurrentLargeOmission
import FiniteAvalanches.Sandpile.Components.CutSites
import FiniteAvalanches.Sandpile.SourceCounting.RadiusReduction
import FiniteAvalanches.Paper.Current.InjectionOutflow

namespace FiniteAvalanches.Sandpile.Components.CurrentCounting
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves FiniteAvalanches.Sandpile.Components MeasureTheory
open scoped Classical ENNReal BigOperators
noncomputable section
theorem large_core_omission_le_cutSites {N : ℕ} (o : FiniteWired.Active N)
    (S : Finset (FiniteWired.Active N)) (B : Finset Site2)
    (F : Finset (FiniteWired.Edge N))
    (hF : ∀ y ∈ S, (WiredTrees.graph N).reaches F (some o) (some y)) :
    (puncturedCountingMeasure o).real {g |
      ¬markedSites S ⊆ core g.val ∧ ¬core g.val ⊆ B} ≤
    ∑ f ∈ F, (WiredTrees.law N).real {t |
      f ∈ (WiredTrees.graph N).rootPathCopies t (some o) none ∧ ¬cutSites o t f ⊆ B} := by
  have he : ∀ f : FiniteWired.Edge N,
      {t : (WiredTrees.graph N).SpanningTree |
        f ∈ (WiredTrees.graph N).rootPathCopies t (some o) none ∧
          ¬(WiredTrees.graph N).componentAfter t.val f (some o) ⊆
            {v : FiniteWired.Vertex N | insideVertex B v}} =
      {t | f ∈ (WiredTrees.graph N).rootPathCopies t (some o) none ∧
        ¬cutSites o t f ⊆ B} := by
    intro f
    ext t
    simp only [Set.mem_setOf_eq]
    by_cases hf : f ∈ (WiredTrees.graph N).rootPathCopies t (some o) none
    · simp only [hf, true_and, cutSites_subset_iff o t f hf B]
    · simp only [hf, false_and]
  simpa only [he] using large_core_omission_le_path_cuts o S B F hF


end
end FiniteAvalanches.Sandpile.Components.CurrentCounting

namespace FiniteAvalanches.Sandpile.SourceCounting.CurrentFront
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves FiniteAvalanches.Sandpile.Components MeasureTheory
open FiniteAvalanches.Sandpile.SourceCounting
open scoped Classical ENNReal BigOperators
noncomputable section

/-- Full inverse excursions, forward restriction and held-burning count, and
the current source-characterized shape-to-tree cut event share one denominator. -/
theorem finite_source_counting {N r M : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N) :
    (FiniteWired.law N).real (finiteAvalancheLeaves (origin N) (boxSites M)) ≤
      (∫ t, WiredTrees.reciprocal N (markedVertices (activeMarks N r))
        (marked_vertices_nonempty _ (source_mem_activeMarks N r)) t ∂WiredTrees.law N) +
      ∑ f ∈ sourceEdges N r hrN, (WiredTrees.law N).real {t |
        f ∈ (WiredTrees.graph N).rootPathCopies t (some (origin N)) none ∧
          ¬cutSites (origin N) t f ⊆ boxSites M} := by
  let S := activeMarks N r
  have hN := marked_neighborhood hr hrN
  have h := finite_avalanche_leaves_probability_le_held (origin N) (markedSites S)
    (boxSites M) (fun x hx => hN (Finset.mem_insert_of_mem hx))
  rw [add_div] at h
  have he :
      (∑ g : Punctured N (origin N),
        (if ¬markedSites S ⊆ core g.val ∧ ¬core g.val ⊆ boxSites M then 1 else 0 : ℝ)) /
          Fintype.card (FiniteWired.Recurrent N) =
      (puncturedCountingMeasure (origin N)).real
        {g | ¬markedSites S ⊆ core g.val ∧ ¬core g.val ⊆ boxSites M} := by
    rw [punctured_counting_real_eq_normalized_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro g _
    by_cases hg : ¬markedSites S ⊆ core g.val ∧ ¬core g.val ⊆ boxSites M
    · simp only [Set.mem_setOf_eq, hg]
    · simp only [Set.mem_setOf_eq, hg, if_false]
  rw [he] at h
  exact h.trans (add_le_add
    (Paper.InjectionOutflow.normalized_held_omissions_le_reciprocal (origin N) S hN)
    (Components.CurrentCounting.large_core_omission_le_cutSites (origin N) S (boxSites M)
      (sourceEdges N r hrN) (sourceEdges_reaches_marks hr hrN)))

/-- Actual finite field radius event, with its determining-volume condition. -/
theorem finiteFieldLaw_origin_radius_probability_le {N r M : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) (hMN : M + 1 ≤ N) :
    (FiniteWired.finiteFieldLaw N).real {η | (M : WithTop ℕ) < radius η 0} ≤
      (∫ t, WiredTrees.reciprocal N (markedVertices (activeMarks N r))
        (marked_vertices_nonempty _ (source_mem_activeMarks N r)) t ∂WiredTrees.law N) +
      ∑ f ∈ sourceEdges N r hrN, (WiredTrees.law N).real {t |
        f ∈ (WiredTrees.graph N).rootPathCopies t (some (origin N)) none ∧
          ¬cutSites (origin N) t f ⊆ boxSites M} := by
  have hr0 : siteRadius 0 (FiniteWired.site (origin N)) = 0 := by
    apply Nat.eq_zero_of_le_zero
    rw [siteRadius_le_iff, site_origin]
    simp
  have hn : siteRadius 0 (FiniteWired.site (origin N)) + M + 1 ≤ N := by
    rw [hr0]
    simpa only [zero_add] using hMN
  have he := finiteFieldLaw_radius_tail_eq_wired (origin N) M hn
  simp only [site_origin, add_zero, Finset.image_id'] at he
  change (FiniteWired.finiteFieldLaw N {η | (M : WithTop ℕ) < radius η 0}).toReal ≤ _
  rw [he]
  exact finite_source_counting hr hrN

end
end FiniteAvalanches.Sandpile.SourceCounting.CurrentFront

#print axioms FiniteAvalanches.Sandpile.Components.CurrentCounting.puncturedForestEquiv
#print axioms FiniteAvalanches.Sandpile.Components.CurrentCounting.crossing_core_mass_eq_tree_cut
#print axioms FiniteAvalanches.Sandpile.SourceCounting.CurrentFront.finite_source_counting
#print axioms FiniteAvalanches.Sandpile.SourceCounting.CurrentFront.finiteFieldLaw_origin_radius_probability_le
