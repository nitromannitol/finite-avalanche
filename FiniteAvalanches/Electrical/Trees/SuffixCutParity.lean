import FiniteAvalanches.Electrical.Trees.ForestComponents
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-! A suffix path between the two forest roots crosses their component cut oddly. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
open scoped Classical BigOperators
noncomputable section

private theorem sum_path_differences {A : Type} [AddCommGroup A] {m : ℕ}
    (g : Fin (m + 1) → A) :
    (∑ k : Fin m, (g k.castSucc - g k.succ)) = g 0 - g (Fin.last m) := by
  have hleft := Fin.sum_univ_castSucc g
  have hright := Fin.sum_univ_succ g
  have ha : (∑ k : Fin m, g k.castSucc) = (∑ k : Fin (m + 1), g k) - g (Fin.last m) :=
    (eq_sub_iff_add_eq).mpr hleft.symm
  have hb : (∑ k : Fin m, g k.succ) = (∑ k : Fin (m + 1), g k) - g 0 :=
    (eq_sub_iff_add_eq).mpr ((add_comm _ _).trans hright.symm)
  rw [Finset.sum_sub_distrib, ha, hb]
  abel

private theorem sum_suffix_differences {A : Type} [AddCommGroup A] {m : ℕ}
    (g : Fin (m + 1) → A) (i : Fin (m + 1)) :
    (∑ k : Fin m, if i.val ≤ k.val then g k.castSucc - g k.succ else 0) =
      g i - g (Fin.last m) := by
  let h : Fin (m + 1) → A := fun k => if k.val < i.val then g i else g k
  have heq (k : Fin m) : h k.castSucc - h k.succ =
      if i.val ≤ k.val then g k.castSucc - g k.succ else 0 := by
    by_cases hk : i.val ≤ k.val
    · simp only [h, Fin.val_castSucc, Fin.val_succ, if_pos hk,
        if_neg (by omega : ¬k.val < i.val), if_neg (by omega : ¬k.val + 1 < i.val)]
    · have hk' : k.val < i.val := by omega
      by_cases he : k.val + 1 = i.val
      · have hi : k.succ = i := Fin.ext he
        simp only [h, Fin.val_castSucc, if_pos hk', hi, lt_self_iff_false, if_false,
          sub_self, if_neg hk]
      · simp only [h, Fin.val_castSucc, Fin.val_succ, if_pos hk',
          if_pos (by omega : k.val + 1 < i.val), sub_self, if_neg hk]
  rw [← Finset.sum_congr rfl (fun k _ => heq k)]
  rw [sum_path_differences]
  have h0 : h 0 = g i := by
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext hi
      simp only [h, Fin.val_zero, hi', lt_self_iff_false, if_false]
    · simp only [h, Fin.val_zero, if_pos (by omega : 0 < i.val)]
  have hm : h (Fin.last m) = g (Fin.last m) := by
    simp only [h, Fin.val_last, if_neg (by omega : ¬m < i.val)]
  rw [h0, hm]

variable {V E : Type}

/-- The once-per-copy suffix cut count has residue one modulo two. -/
theorem twoRootForest_suffix_cut_parity (J : CopiedGraph V E) (m : ℕ)
    (vertices : Fin (m + 1) → V) (copies : Fin m → E)
    (hends : ∀ k : Fin m,
      (J.left (copies k) = vertices k.castSucc ∧ J.right (copies k) = vertices k.succ) ∨
      (J.right (copies k) = vertices k.castSucc ∧ J.left (copies k) = vertices k.succ))
    (i : Fin (m + 1)) (hne : vertices i ≠ vertices (Fin.last m))
    (F : J.TwoRootForest (vertices i) (vertices (Fin.last m))) :
    (∑ k : Fin m, if i.val ≤ k.val ∧
      ¬J.reaches F.val (J.left (copies k)) (J.right (copies k)) then (1 : ZMod 2) else 0) = 1 := by
  let g : V → ZMod 2 := fun x => if J.reaches F.val x (vertices i) then 1 else 0
  have hcut (x y : V) :
      (if ¬J.reaches F.val x y then (1 : ZMod 2) else 0) = g x - g y := by
    rw [twoRootForest_reaches_iff J _ _ F x y]
    by_cases hx : J.reaches F.val x (vertices i) <;>
      by_cases hy : J.reaches F.val y (vertices i) <;>
      simp only [g, hx, hy, true_iff, false_iff, not_true_eq_false,
        not_false_eq_true, if_true, if_false] <;> norm_num
    exact (ZMod.neg_eq_self_mod_two 1).symm
  have hterm (k : Fin m) :
      (if i.val ≤ k.val ∧ ¬J.reaches F.val (J.left (copies k)) (J.right (copies k))
        then (1 : ZMod 2) else 0) =
      if i.val ≤ k.val then g (vertices k.castSucc) - g (vertices k.succ) else 0 := by
    by_cases hk : i.val ≤ k.val
    · rw [if_pos hk]
      simp only [hk, true_and]
      rcases hends k with ⟨ha, hb⟩ | ⟨hb, ha⟩
      · rw [hcut, ha, hb]
      · rw [hcut, ha, hb]
        by_cases hx : J.reaches F.val (vertices k.castSucc) (vertices i) <;>
          by_cases hy : J.reaches F.val (vertices k.succ) (vertices i) <;>
          simp only [g, hx, hy, if_true, if_false] <;> norm_num
        all_goals exact ZMod.neg_eq_self_mod_two 1
    · simp only [hk, false_and, if_false]
  rw [Finset.sum_congr rfl (fun k _ => hterm k),
    sum_suffix_differences (fun k => g (vertices k)) i]
  have hlast : ¬J.reaches F.val (vertices (Fin.last m)) (vertices i) := fun h =>
    twoRootForest_roots_separated J _ _ hne F (TwoCopy.reaches_symm J h)
  simp only [g, if_neg hlast, sub_zero]
  exact if_pos (Relation.ReflTransGen.refl : J.reaches F.val (vertices i) (vertices i))

end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
