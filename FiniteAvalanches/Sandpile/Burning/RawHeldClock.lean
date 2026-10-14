import FiniteAvalanches.Sandpile.Recurrence.RawGraphCarrier
import FiniteAvalanches.Sandpile.Burning.Layers

/-! Parallel held burning on the whole signed integer carrier. -/
namespace FiniteAvalanches.Sandpile.RawGraph
open FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : FiniteAvalanches.Trees.Multigraph V E) (s : V)

def heldClosed (η : Field s) (B A : Finset (Burning.SourceVertex s)) : Prop :=
  B ⊆ A ∧ ∀ x ∈ A, x ∉ B → η x < (Burning.activeDegree G (Finset.univ.erase s) A x : ℤ)

/-- Sink burnt at time zero; each later test uses the entire start-of-step set. -/
def rawParallelRemainder (η : Field s) (B : Finset (Burning.SourceVertex s)) :
    ℕ → Finset (Burning.SourceVertex s)
  | 0 => Finset.univ
  | n + 1 => (rawParallelRemainder η B n).filter fun x =>
      x ∈ B ∨ η x < (Burning.activeDegree G (Finset.univ.erase s)
        (rawParallelRemainder η B n) x : ℤ)

theorem raw_remainder_succ_subset (η : Field s) (B : Finset (Burning.SourceVertex s)) (n : ℕ) :
    rawParallelRemainder G s η B (n + 1) ⊆ rawParallelRemainder G s η B n :=
  Finset.filter_subset _ _

theorem raw_remainder_contains_held (η : Field s) (B : Finset (Burning.SourceVertex s)) (n : ℕ) :
    B ⊆ rawParallelRemainder G s η B n := by
  induction n with
  | zero => exact Finset.subset_univ _
  | succ n ih =>
    intro x hx
    exact Finset.mem_filter.mpr ⟨ih hx, Or.inl hx⟩

theorem raw_initial_image (η : Field s) (B : Finset (Burning.SourceVertex s)) :
    (rawParallelRemainder G s η B 0).image Subtype.val = Finset.univ.erase s :=
  Burning.source_vertices_image s

theorem sink_not_in_raw_remainder (η : Field s) (B : Finset (Burning.SourceVertex s)) (n : ℕ) :
    s ∉ (rawParallelRemainder G s η B n).image Subtype.val :=
  Burning.source_shape_avoids_sink s _

theorem raw_fixed_succ (η : Field s) (B : Finset (Burning.SourceVertex s)) (n : ℕ)
    (hf : rawParallelRemainder G s η B (n + 1) = rawParallelRemainder G s η B n) :
    rawParallelRemainder G s η B (n + 2) = rawParallelRemainder G s η B (n + 1) := by
  change (rawParallelRemainder G s η B (n + 1)).filter _ = _
  rw [hf]
  exact hf

theorem raw_card_bound_or_fixed (η : Field s) (B : Finset (Burning.SourceVertex s)) (n : ℕ) :
    rawParallelRemainder G s η B (n + 1) = rawParallelRemainder G s η B n ∨
      (rawParallelRemainder G s η B n).card + n ≤ Fintype.card (Burning.SourceVertex s) := by
  induction n with
  | zero =>
    right
    simp only [rawParallelRemainder, Finset.card_univ, Nat.add_zero, le_refl]
  | succ n ih =>
    by_cases hf : rawParallelRemainder G s η B (n + 1) = rawParallelRemainder G s η B n
    · exact Or.inl (raw_fixed_succ G s η B n hf)
    · have hb := ih.resolve_left hf
      have hc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨raw_remainder_succ_subset G s η B n, hf⟩)
      right
      omega

theorem raw_fixed_card (η : Field s) (B : Finset (Burning.SourceVertex s)) :
    rawParallelRemainder G s η B (Fintype.card (Burning.SourceVertex s) + 1) =
      rawParallelRemainder G s η B (Fintype.card (Burning.SourceVertex s)) := by
  rcases raw_card_bound_or_fixed G s η B (Fintype.card (Burning.SourceVertex s)) with hf | hc
  · exact hf
  · have he : rawParallelRemainder G s η B (Fintype.card (Burning.SourceVertex s)) = ∅ :=
      Finset.card_eq_zero.mp (by omega)
    apply Finset.Subset.antisymm
    · exact raw_remainder_succ_subset G s η B _
    · rw [he]
      exact Finset.empty_subset _

theorem raw_closed_subset_remainder (η : Field s) (B D : Finset (Burning.SourceVertex s))
    (hd : heldClosed G s η B D) (n : ℕ) : D ⊆ rawParallelRemainder G s η B n := by
  induction n with
  | zero => exact Finset.subset_univ _
  | succ n ih =>
    intro x hx
    refine Finset.mem_filter.mpr ⟨ih hx, ?_⟩
    by_cases hb : x ∈ B
    · exact Or.inl hb
    · exact Or.inr ((hd.2 x hx hb).trans_le (by
        exact_mod_cast Burning.active_degree_mono G (Finset.univ.erase s) ih x))

/-- A literal endpoint of the proved finite clock, on every integer field. -/
def rawHeldBurning (η : Field s) (B : Finset (Burning.SourceVertex s)) :
    Finset (Burning.SourceVertex s) :=
  rawParallelRemainder G s η B (Fintype.card (Burning.SourceVertex s))

theorem raw_terminal_largest (η : Field s) (B : Finset (Burning.SourceVertex s)) :
    heldClosed G s η B (rawHeldBurning G s η B) ∧
      ∀ D, heldClosed G s η B D → D ⊆ rawHeldBurning G s η B := by
  have hc : heldClosed G s η B (rawHeldBurning G s η B) := by
    refine ⟨raw_remainder_contains_held G s η B _, ?_⟩
    intro x hx hb
    have hx' : x ∈ rawParallelRemainder G s η B (Fintype.card (Burning.SourceVertex s) + 1) :=
      (raw_fixed_card G s η B).symm ▸ hx
    exact (Finset.mem_filter.mp hx').2.resolve_left hb
  exact ⟨hc, fun D hd => raw_closed_subset_remainder G s η B D hd _⟩

theorem raw_terminal_eq_iff (η : Field s) (B A : Finset (Burning.SourceVertex s)) :
    rawHeldBurning G s η B = A ↔
      heldClosed G s η B A ∧ ∀ D, heldClosed G s η B D → D ⊆ A := by
  constructor
  · rintro rfl
    exact raw_terminal_largest G s η B
  · rintro ⟨hc, hmax⟩
    exact Finset.Subset.antisymm (hmax _ (raw_terminal_largest G s η B).1)
      ((raw_terminal_largest G s η B).2 A hc)

theorem exists_unique_raw_terminal (η : Field s) (B : Finset (Burning.SourceVertex s)) :
    ∃! A, heldClosed G s η B A ∧ ∀ D, heldClosed G s η B D → D ⊆ A := by
  exact ⟨rawHeldBurning G s η B, raw_terminal_largest G s η B,
    fun A hA => ((raw_terminal_eq_iff G s η B A).mpr hA).symm⟩

theorem raw_remainder_stopped (η : Field s) (B : Finset (Burning.SourceVertex s)) (n : ℕ) :
    rawParallelRemainder G s η B (Fintype.card (Burning.SourceVertex s) + n) =
      rawHeldBurning G s η B := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let step (A : Finset (Burning.SourceVertex s)) := A.filter fun x =>
      x ∈ B ∨ η x < (Burning.activeDegree G (Finset.univ.erase s) A x : ℤ)
    have hf : step (rawHeldBurning G s η B) = rawHeldBurning G s η B :=
      raw_fixed_card G s η B
    calc
      _ = step (rawParallelRemainder G s η B (Fintype.card (Burning.SourceVertex s) + n)) := rfl
      _ = step (rawHeldBurning G s η B) := congrArg step ih
      _ = _ := hf

/-- The exact source stable domain has no lower height bound. -/
def sourceHeldParallelRemainder (η : StableState G s) (B : Finset (Burning.SourceVertex s)) :=
  rawParallelRemainder G s η.val B

def sourceHeldBurning (η : StableState G s) (B : Finset (Burning.SourceVertex s)) :=
  rawHeldBurning G s η.val B

theorem source_terminal_characterization (η : StableState G s) (B A : Finset (Burning.SourceVertex s)) :
    sourceHeldBurning G s η B = A ↔
      heldClosed G s η.val B A ∧ ∀ D, heldClosed G s η.val B D → D ⊆ A :=
  raw_terminal_eq_iff G s η.val B A

/-- Negative heights fail every unheld test, independent of recurrence or stability. -/
theorem negative_height_unburned (η : Field s) (B : Finset (Burning.SourceVertex s))
    (x : Burning.SourceVertex s) (hx : η x < 0) (n : ℕ) :
    x ∈ rawParallelRemainder G s η B n := by
  induction n with
  | zero => exact Finset.mem_univ _
  | succ n ih =>
    exact Finset.mem_filter.mpr ⟨ih, Or.inr (hx.trans_le (Nat.cast_nonneg _))⟩

end
end FiniteAvalanches.Sandpile.RawGraph
