import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! Telescoping on an entire finite vertex sequence, including empty edge sequences. -/
namespace FiniteAvalanches.Electrical
open scoped BigOperators

/-- A suffix of the successive differences of a finite sequence. -/
theorem sum_suffix_sub (m : ℕ) (f : Fin (m+1) → ℝ) (i : Fin (m+1)) :
    (∑ j : Fin m, if i.val ≤ j.val then f j.castSucc-f j.succ else 0) = f i-f (Fin.last m) := by
  induction m with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    simp [hi]
  | succ m ih =>
    refine Fin.lastCases ?_ (fun i => ?_) i
    · have hz : (∑ j : Fin (m+1), if (Fin.last (m+1)).val ≤ j.val then f j.castSucc-f j.succ else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [if_neg (by simp only [Fin.val_last]; omega)]
      rw [hz,sub_self]
    · rw [Fin.sum_univ_castSucc]
      have h := ih (fun k => f k.castSucc) i
      have hi : i.val ≤ m := Nat.le_of_lt_succ i.isLt
      simp only [Fin.val_castSucc,Fin.val_last,if_pos hi]
      change (∑ j : Fin m, if i.val ≤ j.val then f j.castSucc.castSucc-f j.succ.castSucc else 0) +
        (f (Fin.last m).castSucc-f (Fin.last (m+1))) = f i.castSucc-f (Fin.last (m+1))
      rw [h]
      ring

/-- A prefix of successive differences, with the endpoint included as a vertex only. -/
theorem sum_prefix_sub (m : ℕ) (f : Fin (m+1) → ℝ) (i : Fin (m+1)) :
    (∑ j : Fin m, if j.val < i.val then f j.castSucc-f j.succ else 0) = f 0-f i := by
  have hall := sum_suffix_sub m f 0
  simp only [Fin.val_zero,Nat.zero_le,if_true] at hall
  have hsuf := sum_suffix_sub m f i
  have hsplit : (∑ j : Fin m, (f j.castSucc-f j.succ)) =
      (∑ j : Fin m, if j.val < i.val then f j.castSucc-f j.succ else 0) +
      (∑ j : Fin m, if i.val ≤ j.val then f j.castSucc-f j.succ else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : j.val < i.val
    · rw [if_pos h,if_neg (by omega),add_zero]
    · rw [if_neg h,if_pos (by omega),zero_add]
  linarith only [hall,hsuf,hsplit]

/-- The full successive-difference telescope includes the zero-length case. -/
theorem sum_sub_succ (m : ℕ) (f : Fin (m+1) → ℝ) :
    (∑ i : Fin m, (f i.castSucc-f i.succ)) = f 0-f (Fin.last m) := by
  simpa only [Fin.val_zero,Nat.zero_le,if_true] using sum_suffix_sub m f 0

end FiniteAvalanches.Electrical
