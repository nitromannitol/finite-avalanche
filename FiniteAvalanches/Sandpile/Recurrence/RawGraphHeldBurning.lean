import FiniteAvalanches.Sandpile.Recurrence.RawGraphDynamics

/-! The source simultaneous held clock on raw integer heights. The terminal
set is defined by actual finite rounds and characterized before any law is used. -/
namespace FiniteAvalanches.Sandpile.RawGraph
open FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : FiniteAvalanches.Trees.Multigraph V E) (s : V)

def heldParallelRemainder (η : Field s) (B : Finset (Burning.SourceVertex s)) :
    ℕ → Finset (Burning.SourceVertex s)
  | 0 => Finset.univ
  | n + 1 => (heldParallelRemainder η B n).filter fun x =>
      x ∈ B ∨ η x < (Burning.activeDegree G (Finset.univ.erase s)
        (heldParallelRemainder η B n) x : ℤ)

def HeldClosed (η : Field s) (B A : Finset (Burning.SourceVertex s)) : Prop :=
  B ⊆ A ∧ ∀ x ∈ A, x ∉ B → η x < (Burning.activeDegree G (Finset.univ.erase s) A x : ℤ)

theorem held_parallel_succ_subset (η : Field s)
    (B : Finset (Burning.SourceVertex s)) (n : ℕ) :
    heldParallelRemainder G s η B (n + 1) ⊆ heldParallelRemainder G s η B n :=
  Finset.filter_subset _ _

theorem held_parallel_contains_held (η : Field s)
    (B : Finset (Burning.SourceVertex s)) (n : ℕ) : B ⊆ heldParallelRemainder G s η B n := by
  induction n with
  | zero => exact Finset.subset_univ _
  | succ n ih =>
    intro x hx
    exact Finset.mem_filter.mpr ⟨ih hx, Or.inl hx⟩

theorem held_parallel_fixed_succ (η : Field s)
    (B : Finset (Burning.SourceVertex s)) (n : ℕ)
    (hf : heldParallelRemainder G s η B (n + 1) = heldParallelRemainder G s η B n) :
    heldParallelRemainder G s η B (n + 2) = heldParallelRemainder G s η B (n + 1) := by
  change (heldParallelRemainder G s η B (n + 1)).filter _ = _
  rw [hf]
  exact hf

theorem held_parallel_card_bound_or_fixed (η : Field s)
    (B : Finset (Burning.SourceVertex s)) (n : ℕ) :
    heldParallelRemainder G s η B (n + 1) = heldParallelRemainder G s η B n ∨
      (heldParallelRemainder G s η B n).card + n ≤ Fintype.card (Burning.SourceVertex s) := by
  induction n with
  | zero =>
    right
    simp only [heldParallelRemainder, Finset.card_univ, Nat.add_zero, le_refl]
  | succ n ih =>
    by_cases hf : heldParallelRemainder G s η B (n + 1) = heldParallelRemainder G s η B n
    · exact Or.inl (held_parallel_fixed_succ G s η B n hf)
    · have hb := ih.resolve_left hf
      have hc : (heldParallelRemainder G s η B (n + 1)).card <
          (heldParallelRemainder G s η B n).card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
          ⟨held_parallel_succ_subset G s η B n, hf⟩)
      right
      omega

theorem held_parallel_fixed_card (η : Field s) (B : Finset (Burning.SourceVertex s)) :
    heldParallelRemainder G s η B (Fintype.card (Burning.SourceVertex s) + 1) =
      heldParallelRemainder G s η B (Fintype.card (Burning.SourceVertex s)) := by
  rcases held_parallel_card_bound_or_fixed G s η B (Fintype.card (Burning.SourceVertex s)) with hf | hc
  · exact hf
  · have he : heldParallelRemainder G s η B (Fintype.card (Burning.SourceVertex s)) = ∅ :=
      Finset.card_eq_zero.mp (by omega)
    apply Finset.Subset.antisymm
    · exact held_parallel_succ_subset G s η B _
    · rw [he]
      exact Finset.empty_subset _

theorem held_parallel_closed_subset (η : Field s) (B D : Finset (Burning.SourceVertex s))
    (hd : HeldClosed G s η B D) (n : ℕ) : D ⊆ heldParallelRemainder G s η B n := by
  induction n with
  | zero => exact Finset.subset_univ _
  | succ n ih =>
    intro x hx
    refine Finset.mem_filter.mpr ⟨ih hx, ?_⟩
    by_cases hb : x ∈ B
    · exact Or.inl hb
    · have hm := Burning.active_degree_mono G (Finset.univ.erase s) ih x
      have hh := hd.2 x hx hb
      exact Or.inr (by omega)

/-- Full raw source process, selected by its actual simultaneous clock. -/
def heldBurning (η : Field s) (B : Finset (Burning.SourceVertex s)) :
    Finset (Burning.SourceVertex s) :=
  heldParallelRemainder G s η B (Fintype.card (Burning.SourceVertex s))

theorem held_burning_largest (η : Field s) (B : Finset (Burning.SourceVertex s)) :
    HeldClosed G s η B (heldBurning G s η B) ∧
      ∀ D, HeldClosed G s η B D → D ⊆ heldBurning G s η B := by
  constructor
  · refine ⟨held_parallel_contains_held G s η B _, ?_⟩
    intro x hx hb
    have hx' : x ∈ heldParallelRemainder G s η B (Fintype.card (Burning.SourceVertex s) + 1) :=
      (held_parallel_fixed_card G s η B).symm ▸ hx
    exact (Finset.mem_filter.mp hx').2.resolve_left hb
  · intro D hd
    exact held_parallel_closed_subset G s η B D hd _

theorem held_burning_unique (η : Field s) (B A : Finset (Burning.SourceVertex s))
    (hA : HeldClosed G s η B A) (hmax : ∀ D, HeldClosed G s η B D → D ⊆ A) :
    A = heldBurning G s η B := by
  have hf := held_burning_largest G s η B
  exact Finset.Subset.antisymm (hf.2 A hA) (hmax _ hf.1)

/-- Literal raw inequalities commute with every value-preserving finite encoding. -/
theorem held_closed_encoding (η : Field s) (h : Burning.SourceHeights G s)
    (hv : ∀ x, ((h x).val : ℤ) = η x) (B A : Finset (Burning.SourceVertex s)) :
    HeldClosed G s η B A ↔ Burning.heldClosed G (Finset.univ.erase s) h B A := by
  constructor
  · rintro ⟨hBA, ha⟩
    refine ⟨hBA, ?_⟩
    intro x hx hb
    have hh := ha x hx hb
    rw [← hv x] at hh
    exact_mod_cast hh
  · rintro ⟨hBA, ha⟩
    refine ⟨hBA, ?_⟩
    intro x hx hb
    rw [← hv x]
    exact_mod_cast ha x hx hb

/-- Final-set equivalence is proved, rather than postulated by the law definition. -/
theorem held_burning_encoding (η : Field s) (h : Burning.SourceHeights G s)
    (hv : ∀ x, ((h x).val : ℤ) = η x) (B : Finset (Burning.SourceVertex s)) :
    heldBurning G s η B = Burning.heldBurning G (Finset.univ.erase s) h B := by
  symm
  apply held_burning_unique G s η B _
  · exact (held_closed_encoding G s η h hv B _).mpr
      (Burning.held_burning_largest G (Finset.univ.erase s) h B).1
  · intro D hd
    exact (Burning.held_burning_largest G (Finset.univ.erase s) h B).2 D
      ((held_closed_encoding G s η h hv B D).mp hd)

end
end FiniteAvalanches.Sandpile.RawGraph
