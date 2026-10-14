import FiniteAvalanches.Sandpile.Burning.SourceFields

/-! Parallel held burning has the same terminal set as sequential burning. -/

namespace FiniteAvalanches.Sandpile.Burning
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : FiniteAvalanches.Trees.Multigraph V E) (s : V)

/-- The unburned nonsink vertices after the given number of parallel steps. -/
def heldParallelRemainder (h : SourceHeights G s) (B : Finset (SourceVertex s)) :
    ℕ → Finset (SourceVertex s)
  | 0 => Finset.univ
  | n + 1 => (heldParallelRemainder h B n).filter fun x =>
      x ∈ B ∨ (h x).val < activeDegree G (Finset.univ.erase s)
        (heldParallelRemainder h B n) x

theorem held_parallel_succ_subset (h : SourceHeights G s)
    (B : Finset (SourceVertex s)) (n : ℕ) :
    heldParallelRemainder G s h B (n + 1) ⊆ heldParallelRemainder G s h B n :=
  Finset.filter_subset _ _

theorem held_parallel_contains_held (h : SourceHeights G s)
    (B : Finset (SourceVertex s)) (n : ℕ) : B ⊆ heldParallelRemainder G s h B n := by
  induction n with
  | zero => exact Finset.subset_univ _
  | succ n ih =>
    intro x hx
    exact Finset.mem_filter.mpr ⟨ih hx, Or.inl hx⟩

theorem held_parallel_fixed_succ (h : SourceHeights G s)
    (B : Finset (SourceVertex s)) (n : ℕ)
    (hf : heldParallelRemainder G s h B (n + 1) = heldParallelRemainder G s h B n) :
    heldParallelRemainder G s h B (n + 2) = heldParallelRemainder G s h B (n + 1) := by
  change (heldParallelRemainder G s h B (n + 1)).filter _ = _
  rw [hf]
  exact hf

theorem held_parallel_card_bound_or_fixed (h : SourceHeights G s)
    (B : Finset (SourceVertex s)) (n : ℕ) :
    heldParallelRemainder G s h B (n + 1) = heldParallelRemainder G s h B n ∨
      (heldParallelRemainder G s h B n).card + n ≤ Fintype.card (SourceVertex s) := by
  induction n with
  | zero =>
    right
    simp only [heldParallelRemainder, Finset.card_univ, Nat.add_zero, le_refl]
  | succ n ih =>
    by_cases hf : heldParallelRemainder G s h B (n + 1) = heldParallelRemainder G s h B n
    · exact Or.inl (held_parallel_fixed_succ G s h B n hf)
    · have hb := ih.resolve_left hf
      have hc : (heldParallelRemainder G s h B (n + 1)).card <
          (heldParallelRemainder G s h B n).card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
          ⟨held_parallel_succ_subset G s h B n, hf⟩)
      right
      omega

theorem held_parallel_fixed_card (h : SourceHeights G s)
    (B : Finset (SourceVertex s)) :
    heldParallelRemainder G s h B (Fintype.card (SourceVertex s) + 1) =
      heldParallelRemainder G s h B (Fintype.card (SourceVertex s)) := by
  rcases held_parallel_card_bound_or_fixed G s h B (Fintype.card (SourceVertex s)) with hf | hc
  · exact hf
  · have he : heldParallelRemainder G s h B (Fintype.card (SourceVertex s)) = ∅ :=
      Finset.card_eq_zero.mp (by omega)
    apply Finset.Subset.antisymm
    · exact held_parallel_succ_subset G s h B _
    · rw [he]
      exact Finset.empty_subset _

theorem held_parallel_closed_subset (h : SourceHeights G s)
    (B D : Finset (SourceVertex s))
    (hd : heldClosed G (Finset.univ.erase s) h B D) (n : ℕ) :
    D ⊆ heldParallelRemainder G s h B n := by
  induction n with
  | zero => exact Finset.subset_univ _
  | succ n ih =>
    intro x hx
    refine Finset.mem_filter.mpr ⟨ih hx, ?_⟩
    by_cases hb : x ∈ B
    · exact Or.inl hb
    · exact Or.inr ((hd.2 x hx hb).trans_le
        (active_degree_mono G (Finset.univ.erase s) ih x))

/-- The whole parallel terminal set, with no certificate premise. -/
theorem held_parallel_final_eq (h : SourceHeights G s)
    (B : Finset (SourceVertex s)) :
    heldParallelRemainder G s h B (Fintype.card (SourceVertex s)) =
      heldBurning G (Finset.univ.erase s) h B := by
  let A := heldParallelRemainder G s h B (Fintype.card (SourceVertex s))
  have hclosed : heldClosed G (Finset.univ.erase s) h B A := by
    refine ⟨held_parallel_contains_held G s h B _, ?_⟩
    intro x hx hb
    have hx' : x ∈ heldParallelRemainder G s h B (Fintype.card (SourceVertex s) + 1) :=
      (held_parallel_fixed_card G s h B).symm ▸ hx
    exact (Finset.mem_filter.mp hx').2.resolve_left hb
  exact Finset.Subset.antisymm
    ((held_burning_largest G (Finset.univ.erase s) h B).2 A hclosed)
    (held_parallel_closed_subset G s h B _
      (held_burning_largest G (Finset.univ.erase s) h B).1 _)

end
end FiniteAvalanches.Sandpile.Burning
