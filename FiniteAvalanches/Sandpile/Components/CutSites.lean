import FiniteAvalanches.Sandpile.Components.LargeOmission

/-! The deletion component's active lattice carrier is literal, with the sink
excluded by the proved root-path criterion whenever it is used in a cut event. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Sandpile.Waves MeasureTheory
open scoped Classical ENNReal
noncomputable section

def cutSites {N : ℕ} (o : FiniteWired.Active N)
    (t : (WiredTrees.graph N).SpanningTree) (f : FiniteWired.Edge N) : Finset Site2 :=
  ((Finset.univ : Finset (FiniteWired.Active N)).filter fun x =>
    (WiredTrees.graph N).reaches (t.val.erase f) (some o) (some x)).image FiniteWired.site

theorem mem_cutSites {N : ℕ} (o : FiniteWired.Active N)
    (t : (WiredTrees.graph N).SpanningTree) (f : FiniteWired.Edge N)
    (x : FiniteWired.Active N) :
    FiniteWired.site x ∈ cutSites o t f ↔
      (WiredTrees.graph N).reaches (t.val.erase f) (some o) (some x) := by
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
    have hxy := FiniteWired.site_injective N he
    subst y
    exact (Finset.mem_filter.mp hy).2
  · intro hx
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩

theorem cutSites_subset_iff {N : ℕ} (o : FiniteWired.Active N)
    (t : (WiredTrees.graph N).SpanningTree) (f : FiniteWired.Edge N)
    (hf : f ∈ (WiredTrees.graph N).rootPathCopies t (some o) none) (B : Finset Site2) :
    cutSites o t f ⊆ B ↔
      (WiredTrees.graph N).componentAfter t.val f (some o) ⊆
        {v : FiniteWired.Vertex N | insideVertex B v} := by
  have hn := ((WiredTrees.graph N).mem_rootPathCopies t (some o) none f).mp hf
  constructor
  · intro h v hv
    cases v with
    | none => exact (hn.2 hv).elim
    | some x => exact h ((mem_cutSites o t f x).mpr hv)
  · intro h z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact h (Finset.mem_filter.mp hx).2

/-- The deletion event is the manuscript's literal lattice cut-component event. -/
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
end FiniteAvalanches.Sandpile.Components

namespace FiniteAvalanches.Sandpile.Waves
open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Sandpile.Components MeasureTheory
open scoped Classical ENNReal
noncomputable section

/-- The finite counting estimate has the exact reciprocal and lattice cut-component terms. -/
theorem finite_avalanche_leaves_probability_le_reciprocal_add_cutSites {N : ℕ}
    (o : FiniteWired.Active N) (S : Finset (FiniteWired.Active N)) (B : Finset Site2)
    (F : Finset (FiniteWired.Edge N))
    (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ markedSites S)
    (hF : ∀ y ∈ S, (WiredTrees.graph N).reaches F (some o) (some y)) :
    (FiniteWired.law N).real (finiteAvalancheLeaves o B) ≤
      (∫ t, WiredTrees.reciprocal N (markedVertices S)
        (marked_vertices_nonempty S (Marked.source_mem_of_marked_neighbors S hN)) t
        ∂WiredTrees.law N) +
      ∑ f ∈ F, (WiredTrees.law N).real {t |
        f ∈ (WiredTrees.graph N).rootPathCopies t (some o) none ∧ ¬cutSites o t f ⊆ B} :=
  (finite_avalanche_leaves_probability_le_reciprocal_add_omission o S B hN).trans
    (add_le_add le_rfl (large_core_omission_le_cutSites o S B F hF))

end
end FiniteAvalanches.Sandpile.Waves
