import FiniteAvalanches.Sandpile.Components.CurrentEdgeInsertion
import FiniteAvalanches.Sandpile.Components.ForwardEdgeInsertion
import FiniteAvalanches.Trees.PathCopies

/-! The finite large-core omission estimate is a tagged crossing-edge union,
so multiple crossings increase the bound rather than being silently discarded. -/
namespace FiniteAvalanches.Sandpile.Components.CurrentCounting
open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Sandpile.Waves MeasureTheory
open FiniteAvalanches.Sandpile.Components
open scoped Classical ENNReal
noncomputable section

/-- A lattice shape and its full original active-vertex support have the same containment. -/
theorem inside_support_subset_iff {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (B : Finset Site2) :
    insideSupport C ⊆ {v : FiniteWired.Vertex N | insideVertex B v} ↔ C.val ⊆ B := by
  constructor
  · intro h x hx
    let a := FiniteWired.activeOfSite N x ((mem_box_sites N x).mp (C.property.1 hx))
    exact h (show some a ∈ insideSupport C from hx)
  · intro h v hv
    cases v with
    | none => exact hv.elim
    | some x => exact h hv

/-- A fixed genuine copied path to a missing marked vertex crosses the actual core. -/
theorem exists_core_crossing {N : ℕ} (o : FiniteWired.Active N)
    (S : Finset (FiniteWired.Active N)) (F : Finset (FiniteWired.Edge N))
    (hF : ∀ y ∈ S, (WiredTrees.graph N).reaches F (some o) (some y))
    (g : Punctured N o) (hm : ¬markedSites S ⊆ core g.val) :
    ∃ f ∈ F, (WiredTrees.graph N).crosses (insideSupport (coreShape g.val)) f := by
  by_contra hn
  apply hm
  intro z hz
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
  by_contra hc
  exact hn ((WiredTrees.graph N).exists_crossing_of_reaches (hF y hy)
    (coreShape g.val).property.2 hc)

/-- Actual large source cores missing marks are bounded by actual root-path cut events.
F can be the union of fixed original copied paths; no edge is chosen and no copy is quotiented. -/
theorem large_core_omission_le_path_cuts {N : ℕ} (o : FiniteWired.Active N)
    (S : Finset (FiniteWired.Active N)) (B : Finset Site2)
    (F : Finset (FiniteWired.Edge N))
    (hF : ∀ y ∈ S, (WiredTrees.graph N).reaches F (some o) (some y)) :
    (puncturedCountingMeasure o).real {g |
      ¬markedSites S ⊆ core g.val ∧ ¬core g.val ⊆ B} ≤
    ∑ f ∈ F, (WiredTrees.law N).real {t |
      f ∈ (WiredTrees.graph N).rootPathCopies t (some o) none ∧
      ¬(WiredTrees.graph N).componentAfter t.val f (some o) ⊆
        {v : FiniteWired.Vertex N | insideVertex B v}} := by
  let A : FiniteWired.Edge N → Set (Punctured N o) := fun f =>
    {g | (WiredTrees.graph N).crosses (insideSupport (coreShape g.val)) f ∧
      ¬core g.val ⊆ B}
  have hs : {g : Punctured N o | ¬markedSites S ⊆ core g.val ∧ ¬core g.val ⊆ B} ⊆
      ⋃ f ∈ F, A f := by
    intro g hg
    obtain ⟨f, hf, hc⟩ := exists_core_crossing o S F hF g hg.1
    exact Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨hf, hc, hg.2⟩⟩
  calc
    _ ≤ (puncturedCountingMeasure o).real (⋃ f ∈ F, A f) := measureReal_mono hs (measure_ne_top _ _)
    _ ≤ ∑ f ∈ F, (puncturedCountingMeasure o).real (A f) :=
      measureReal_biUnion_finset_le F A
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro f _
      have he := Forward.crossing_core_mass_le_tree_cut o f
        {D | ¬D ⊆ {v : FiniteWired.Vertex N | insideVertex B v}}
      have ha : A f = {g : Punctured N o |
          (WiredTrees.graph N).crosses (insideSupport (coreShape g.val)) f ∧
          insideSupport (coreShape g.val) ∈
            {D | ¬D ⊆ {v : FiniteWired.Vertex N | insideVertex B v}}} := by
        ext g
        simp only [A, Set.mem_setOf_eq, inside_support_subset_iff]
        rfl
      rw [ha]
      simpa only [Set.mem_setOf_eq, (WiredTrees.graph N).mem_rootPathCopies, and_assoc] using he

end
end FiniteAvalanches.Sandpile.Components.CurrentCounting
