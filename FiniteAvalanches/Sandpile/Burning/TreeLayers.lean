module

public import FiniteAvalanches.Sandpile.Burning.TreeHeights

@[expose] public section

/-! Tree-defined heights are allowed by the minimum-distance test. Their actual
burning recursion is now reconstructed globally: remaining vertices have distance
larger than the number of completed nonsink layers, with no supplied layer law. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [LinearOrder E]
    (G : Multigraph V E) (s : V)

def treeRemainder (t : (copiedTreeGraph G).SpanningTree) (n : ℕ) : Finset (SourceVertex s) :=
  Finset.univ.filter fun v => n < treeDistance G s t v.val

theorem tree_remainder_image (t : (copiedTreeGraph G).SpanningTree) (n : ℕ) :
    (treeRemainder G s t n).image Subtype.val =
      Finset.univ.filter fun w => n < treeDistance G s t w := by
  ext w
  constructor
  · intro hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩
  · intro hw
    have hd := (Finset.mem_filter.mp hw).2
    have hws : w ≠ s := by
      intro he
      rw [he, tree_distance_sink] at hd
      omega
    exact Finset.mem_image.mpr ⟨⟨w, Finset.mem_erase.mpr ⟨hws, Finset.mem_univ _⟩⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩, rfl⟩

theorem tree_burn_test (t : (copiedTreeGraph G).SpanningTree) (n : ℕ)
    (v : SourceVertex s) (hv : n < treeDistance G s t v.val) :
    (treeHeights G s t v).val <
      activeDegree G (Finset.univ.erase s) (treeRemainder G s t n) v ↔
      n + 1 < treeDistance G s t v.val := by
  change (treeHeights G s t v).val < degreeInto G _ v.val ↔ _
  rw [tree_remainder_image]
  have hh := tree_heights_interval G s t v
  constructor
  · intro hb
    by_contra hn
    have he : treeDistance G s t v.val = n + 1 := by omega
    have hs : (Finset.univ.filter fun w => n < treeDistance G s t w) =
        Finset.univ.filter fun w => treeDistance G s t v.val ≤ treeDistance G s t w := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [hs] at hb
    change (treeHeights G s t v).val < treeBase G s t v at hb
    omega
  · intro hn
    have hs : (Finset.univ.filter fun w =>
        treeDistance G s t v.val ≤ treeDistance G s t w + 1) ⊆
        Finset.univ.filter fun w => n < treeDistance G s t w := by
      intro w hw
      have hd := (Finset.mem_filter.mp hw).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    exact hh.2.trans_le (degree_into_mono G hs v.val)

/-- Global reconstruction of the actual recursion, rather than a local rank interval. -/
theorem burn_remainder_tree_heights (t : (copiedTreeGraph G).SpanningTree) (n : ℕ) :
    burnRemainder G s (treeHeights G s t) n = treeRemainder G s t n := by
  induction n with
  | zero =>
    ext v
    simp only [burnRemainder, treeRemainder, Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_of_true (by trivial) (tree_distance_pos G s t v)
  | succ n ih =>
    rw [burnRemainder, ih]
    ext v
    simp only [Finset.mem_filter, treeRemainder, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hv, hb⟩
      exact (tree_burn_test G s t n v hv).mp hb
    · intro hv
      have hn : n < treeDistance G s t v.val := by omega
      exact ⟨hn, (tree_burn_test G s t n v hn).mpr hv⟩

theorem burn_layer_tree_heights (t : (copiedTreeGraph G).SpanningTree) (n : ℕ) :
    burnLayer G s (treeHeights G s t) n =
      Finset.univ.filter fun v : SourceVertex s => treeDistance G s t v.val = n + 1 := by
  unfold burnLayer
  rw [burn_remainder_tree_heights, burn_remainder_tree_heights]
  ext v
  simp only [treeRemainder, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

theorem burn_time_tree_heights (t : (copiedTreeGraph G).SpanningTree) (v : SourceVertex s) :
    burnTime G s (treeHeights G s t) (tree_heights_noForbidden G s t) v + 1 =
      treeDistance G s t v.val := by
  have hp := tree_distance_pos G s t v
  have hl : v ∈ burnLayer G s (treeHeights G s t) (treeDistance G s t v.val - 1) := by
    rw [burn_layer_tree_heights]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
  rw [(burn_time_eq_iff G s _ _ v _).mpr hl]
  omega

end
end FiniteAvalanches.Sandpile.Burning
