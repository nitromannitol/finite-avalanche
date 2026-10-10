module

public import FiniteAvalanches.Sandpile.Burning.TreePaths
public import FiniteAvalanches.Sandpile.Burning.TreeLayers
public import FiniteAvalanches.Sandpile.Burning.Ranks

@[expose] public section

/-! The global inverse compares actual remaining sets and previous layers before
comparing ranks. These comparisons preserve every nonsink coordinate and every
original edge copy; no supplied burning schedule is used. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [LinearOrder E]
    (G : Multigraph V E) (s : V)

omit [DecidableEq V] in
theorem tree_distance_zero_iff (t : (copiedTreeGraph G).SpanningTree) (w : V) :
    treeDistance G s t w = 0 ↔ w = s := by
  constructor
  · exact SimpleGraph.Walk.eq_of_length_eq_zero
  · intro he
    rw [he, tree_distance_sink]

omit [LinearOrder E] in
theorem mem_burn_remainder_iff_time (h : SourceHeights G s)
    (hn : noForbidden G (Finset.univ.erase s) h) (n : ℕ) (v : SourceVertex s) :
    v ∈ burnRemainder G s h n ↔ n ≤ burnTime G s h hn v := by
  have hv := Finset.mem_sdiff.mp (burn_time_spec G s h hn v)
  constructor
  · intro hm
    by_contra he
    have ht : burnTime G s h hn v + 1 ≤ n := by omega
    exact hv.2 (burn_remainder_antitone G s h ht hm)
  · intro ht
    exact burn_remainder_antitone G s h ht hv.1

theorem original_remainder_distance (h : SourceHeights G s)
    (hn : noForbidden G (Finset.univ.erase s) h) (n : ℕ) :
    (burnRemainder G s h n).image Subtype.val =
      Finset.univ.filter fun w => n < treeDistance G s (burningTree G s h hn) w := by
  ext w
  constructor
  · intro hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    have ht := (mem_burn_remainder_iff_time G s h hn n v).mp hv
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [tree_distance_burning_tree]; omega⟩
  · intro hw
    have hd := (Finset.mem_filter.mp hw).2
    have hws : w ≠ s := by
      intro he
      rw [he, tree_distance_sink] at hd
      omega
    let v : SourceVertex s := ⟨w, Finset.mem_erase.mpr ⟨hws, Finset.mem_univ _⟩⟩
    have ht : n ≤ burnTime G s h hn v := by
      have he := tree_distance_burning_tree G s h hn v
      change treeDistance G s (burningTree G s h hn) w = _ at he
      omega
    exact Finset.mem_image.mpr ⟨v, (mem_burn_remainder_iff_time G s h hn n v).mpr ht, rfl⟩

theorem original_previous_distance (h : SourceHeights G s)
    (hn : noForbidden G (Finset.univ.erase s) h) (n : ℕ) :
    previousBurnt G s h n =
      Finset.univ.filter fun w => treeDistance G s (burningTree G s h hn) w = n := by
  cases n with
  | zero =>
    ext w
    simp only [previousBurnt, Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ,
      true_and, tree_distance_zero_iff]
  | succ n =>
    ext w
    constructor
    · intro hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      have ht := (burn_time_eq_iff G s h hn v n).mpr hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        rw [tree_distance_burning_tree, ht]⟩
    · intro hw
      have hd := (Finset.mem_filter.mp hw).2
      have hws : w ≠ s := by
        intro he
        rw [he, tree_distance_sink] at hd
        omega
      let v : SourceVertex s := ⟨w, Finset.mem_erase.mpr ⟨hws, Finset.mem_univ _⟩⟩
      have ht : burnTime G s h hn v = n := by
        have he := tree_distance_burning_tree G s h hn v
        change treeDistance G s (burningTree G s h hn) w = _ at he
        omega
      exact Finset.mem_image.mpr ⟨v, (burn_time_eq_iff G s h hn v n).mp ht, rfl⟩

theorem original_tree_base (h : SourceHeights G s)
    (hn : noForbidden G (Finset.univ.erase s) h) (v : SourceVertex s) :
    treeBase G s (burningTree G s h hn) v =
      activeDegree G (Finset.univ.erase s) (burnRemainder G s h (burnTime G s h hn v)) v := by
  unfold treeBase activeDegree
  rw [original_remainder_distance G s h hn, tree_distance_burning_tree G s h hn]
  congr 1

theorem original_tree_parent_copies (h : SourceHeights G s)
    (hn : noForbidden G (Finset.univ.erase s) h) (v : SourceVertex s) :
    treeParentCopies G s (burningTree G s h hn) v =
      parentCopies G s h (burnTime G s h hn v) v := by
  unfold treeParentCopies parentCopies
  rw [original_previous_distance G s h hn, tree_distance_burning_tree G s h hn]
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  omega

/-- First global inverse: every height of the original allowed field is recovered. -/
theorem tree_heights_burning_tree (h : SourceHeights G s)
    (hn : noForbidden G (Finset.univ.erase s) h) :
    treeHeights G s (burningTree G s h hn) = h := by
  funext v
  apply Fin.ext
  rw [tree_height_rank_eq, original_tree_base]
  have hr := copy_rank_congr (original_tree_parent_copies G s h hn v)
    (tree_parent_burning_tree G s h hn v)
    (treeParent G s (burningTree G s h hn) v).property
    (globalParentCopy G s h hn v).property
  rw [hr, Nat.add_comm]
  exact global_parent_rank_reconstruct G s h hn v

end
end FiniteAvalanches.Sandpile.Burning
