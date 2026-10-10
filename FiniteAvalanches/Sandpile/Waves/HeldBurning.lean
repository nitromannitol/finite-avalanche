import FiniteAvalanches.Sandpile.Waves.Forbidden

/-! Deterministic burning with a held set, using actual successive vertex deletions.
This file proves order independence on wired lattice carriers, not the spanning-tree law. -/

namespace FiniteAvalanches.Sandpile.Waves

open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

/-- A possible final unburnt set, with the held vertices exempt from the burn test. -/
def held_closed (h : Site2 → ℤ) (B A : Finset Site2) : Prop :=
  B ⊆ A ∧ ∀ x ∈ A, x ∉ B → h x < (degree A x : ℤ)

/-- Every step burns one eligible, unheld vertex; `nil` means all such vertices fail the test. -/
inductive BurnTrace (h : Site2 → ℤ) (B : Finset Site2) :
    Finset Site2 → List Site2 → Finset Site2 → Prop
  | nil {A} (ht : ∀ x ∈ A, x ∉ B → h x < (degree A x : ℤ)) : BurnTrace h B A [] A
  | cons {A w C x} (hx : x ∈ A) (hb : x ∉ B) (ht : (degree A x : ℤ) ≤ h x)
      (tail : BurnTrace h B (A.erase x) w C) : BurnTrace h B A (x :: w) C

theorem exists_burn_trace (h : Site2 → ℤ) (B A : Finset Site2) :
    ∃ w C, BurnTrace h B A w C := by
  exact go A
where
  go (A : Finset Site2) : ∃ w C, BurnTrace h B A w C := by
    by_cases ht : ∀ x ∈ A, x ∉ B → h x < (degree A x : ℤ)
    · exact ⟨[], A, BurnTrace.nil ht⟩
    · push Not at ht
      obtain ⟨x, hx, hb, ht⟩ := ht
      obtain ⟨w, C, hw⟩ := go (A.erase x)
      exact ⟨x :: w, C, BurnTrace.cons hx hb ht hw⟩
  termination_by A.card
  decreasing_by exact Finset.card_erase_lt_of_mem hx

theorem BurnTrace.final_subset {h : Site2 → ℤ} {B A C : Finset Site2} {w : List Site2}
    (hw : BurnTrace h B A w C) : C ⊆ A := by
  induction hw with
  | nil => exact fun _ hx => hx
  | cons _ _ _ _ ih => exact ih.trans (Finset.erase_subset _ _)

theorem BurnTrace.final_closed {h : Site2 → ℤ} {B A C : Finset Site2} {w : List Site2}
    (hw : BurnTrace h B A w C) (hB : B ⊆ A) : held_closed h B C := by
  induction hw with
  | nil ht => exact ⟨hB, ht⟩
  | @cons A w C x hx hb ht tail ih =>
    apply ih
    intro y hy
    exact Finset.mem_erase.mpr ⟨fun he => hb (he ▸ hy), hB hy⟩

theorem BurnTrace.closed_subset_final {h : Site2 → ℤ} {B A C D : Finset Site2}
    {w : List Site2} (hw : BurnTrace h B A w C) (hD : D ⊆ A)
    (hd : held_closed h B D) : D ⊆ C := by
  induction hw with
  | nil => exact hD
  | @cons A w C x hx hb ht tail ih =>
    apply ih
    intro y hy
    refine Finset.mem_erase.mpr ⟨?_, hD hy⟩
    intro he
    subst y
    have hh := hd.2 x hy hb
    have hm : (degree D x : ℤ) ≤ (degree A x : ℤ) := by exact_mod_cast degree_mono hD x
    omega

theorem BurnTrace.final_unique {h : Site2 → ℤ} {B A C D : Finset Site2}
    {w v : List Site2} (hw : BurnTrace h B A w C) (hv : BurnTrace h B A v D)
    (hB : B ⊆ A) : C = D := by
  apply Finset.Subset.antisymm
  · exact hv.closed_subset_final hw.final_subset (hw.final_closed hB)
  · exact hw.closed_subset_final hv.final_subset (hv.final_closed hB)

theorem exists_unique_burn_final (h : Site2 → ℤ) (B A : Finset Site2) (hB : B ⊆ A) :
    ∃! C, ∃ w, BurnTrace h B A w C := by
  obtain ⟨w, C, hw⟩ := exists_burn_trace h B A
  exact ⟨C, ⟨w, hw⟩, fun D ⟨v, hv⟩ => hv.final_unique hw hB⟩

/-- The final unburnt set, chosen after termination and order independence. -/
def heldBurning (h : Site2 → ℤ) (B A : Finset Site2) (hB : B ⊆ A) : Finset Site2 :=
  (exists_unique_burn_final h B A hB).choose

theorem held_burning_largest (h : Site2 → ℤ) (B A : Finset Site2) (hB : B ⊆ A) :
    held_closed h B (heldBurning h B A hB) ∧ heldBurning h B A hB ⊆ A ∧
      ∀ D ⊆ A, held_closed h B D → D ⊆ heldBurning h B A hB := by
  obtain ⟨w, hw⟩ := (exists_unique_burn_final h B A hB).choose_spec.1
  exact ⟨hw.final_closed hB, hw.final_subset, fun D hD hd => hw.closed_subset_final hD hd⟩

end
end FiniteAvalanches.Sandpile.Waves
