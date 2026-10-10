import FiniteAvalanches.Sandpile.Components.CutSites

/-! A genuine tagged sum over marked vertices and their fixed original-copy paths.
Repeated copies on different paths are retained in the bound. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Sandpile.Waves MeasureTheory
open scoped Classical ENNReal
noncomputable section

theorem large_core_omission_le_marked_path_cuts {N : ℕ} (o : FiniteWired.Active N)
    (S : Finset (FiniteWired.Active N)) (B : Finset Site2)
    (P : FiniteWired.Active N → Finset (FiniteWired.Edge N))
    (hP : ∀ y ∈ S, (WiredTrees.graph N).reaches (P y) (some o) (some y)) :
    (puncturedCountingMeasure o).real {g |
      ¬markedSites S ⊆ core g.val ∧ ¬core g.val ⊆ B} ≤
    ∑ y ∈ S, ∑ f ∈ P y, (WiredTrees.law N).real {t |
      f ∈ (WiredTrees.graph N).rootPathCopies t (some o) none ∧ ¬cutSites o t f ⊆ B} := by
  let A : FiniteWired.Edge N → Set (Punctured N o) := fun f =>
    {g | (WiredTrees.graph N).crosses (insideSupport (coreShape g.val)) f ∧
      ¬core g.val ⊆ B}
  have hs : {g : Punctured N o | ¬markedSites S ⊆ core g.val ∧ ¬core g.val ⊆ B} ⊆
      ⋃ y ∈ S, ⋃ f ∈ P y, A f := by
    intro g hg
    have hm : ¬markedVertices S ⊆ insideSupport (coreShape g.val) := by
      exact fun h => hg.1 ((marked_subset_iff S (coreShape g.val)).mpr h)
    obtain ⟨v, hv, hn⟩ := Set.not_subset.mp hm
    obtain ⟨y, hy, rfl⟩ := hv
    obtain ⟨f, hf, hc⟩ := (WiredTrees.graph N).exists_crossing_of_reaches
      (hP y hy) (coreShape g.val).property.2 hn
    exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy,
      Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨hf, hc, hg.2⟩⟩⟩⟩
  calc
    _ ≤ (puncturedCountingMeasure o).real (⋃ y ∈ S, ⋃ f ∈ P y, A f) :=
      measureReal_mono hs (measure_ne_top _ _)
    _ ≤ ∑ y ∈ S, (puncturedCountingMeasure o).real (⋃ f ∈ P y, A f) :=
      measureReal_biUnion_finset_le S _
    _ ≤ ∑ y ∈ S, ∑ f ∈ P y, (puncturedCountingMeasure o).real (A f) := by
      apply Finset.sum_le_sum
      intro y _
      exact measureReal_biUnion_finset_le (P y) A
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro f _
      have ha : A f = {g : Punctured N o |
          (WiredTrees.graph N).crosses (insideSupport (coreShape g.val)) f ∧
          insideSupport (coreShape g.val) ∈
            {D | ¬D ⊆ {v : FiniteWired.Vertex N | insideVertex B v}}} := by
        ext g
        simp only [A, Set.mem_setOf_eq, inside_support_subset_iff]
        rfl
      rw [ha, crossing_core_mass_eq_tree_cut]
      congr 1
      ext t
      simp only [Set.mem_setOf_eq]
      rw [← and_assoc, ← (WiredTrees.graph N).mem_rootPathCopies]
      exact and_congr_right fun hf => not_congr (cutSites_subset_iff o t f hf B).symm

end
end FiniteAvalanches.Sandpile.Components
