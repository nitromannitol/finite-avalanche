import FiniteAvalanches.Sandpile.Components.Measure
import FiniteAvalanches.Sandpile.Waves.BurnedSet

/-! Partition the actual punctured fields by their full source-containing core. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Sandpile.Waves
open scoped Classical
noncomputable section

/-- Every punctured field belongs to its actual core fiber, and to no other fiber. -/
def coreFieldPartition {N : ℕ} (o : FiniteWired.Active N) :
    Punctured N o ≃ (C : ComponentShape o) × CoreField o C.val where
  toFun h := ⟨coreShape h.val, ⟨h, rfl⟩⟩
  invFun h := h.2.val
  left_inv _ := rfl
  right_inv h := by
    rcases h with ⟨C, h, hh⟩
    have he : coreShape h.val = C := Subtype.ext hh
    cases he
    rfl

/-- The full finite sum is partitioned by actual core shape, including empty fibers. -/
theorem sum_core_fields {N : ℕ} (o : FiniteWired.Active N) (f : Punctured N o → ℝ) :
    (∑ h : Punctured N o, f h) =
      ∑ C : ComponentShape o, ∑ h : CoreField o C.val, f h.val := by
  rw [← Equiv.sum_comp (coreFieldPartition o).symm, Fintype.sum_sigma]
  rfl

/-- Shape containment can be taken outside the actual held-burn omission sum. -/
theorem sum_held_omissions_by_core {N : ℕ} (o : FiniteWired.Active N)
    (S : Finset Site2) :
    (∑ g : Punctured N o,
      (if S ⊆ core g.val ∧ ¬S ⊆ heldInterior g.val (coreShape g.val) then 1 else 0 : ℝ)) =
      ∑ C : ComponentShape o,
        if S ⊆ C.val then
          ∑ g : CoreField o C.val, (if ¬S ⊆ heldInterior g.val.val C then 1 else 0 : ℝ)
        else 0 := by
  rw [sum_core_fields]
  apply Finset.sum_congr rfl
  intro C _
  by_cases hSC : S ⊆ C.val
  · rw [if_pos hSC]
    apply Finset.sum_congr rfl
    intro g _
    have he : coreShape g.val.val = C := Subtype.ext g.property
    rw [he, g.property]
    simp only [hSC, true_and]
  · rw [if_neg hSC]
    apply Finset.sum_eq_zero
    intro g _
    rw [g.property]
    simp only [hSC, false_and, if_false]

end
end FiniteAvalanches.Sandpile.Components
