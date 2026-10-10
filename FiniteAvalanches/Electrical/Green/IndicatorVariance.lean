import FiniteAvalanches.Electrical.Green.PairBound
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
namespace FiniteAvalanches.Electrical
open scoped Classical BigOperators

/-- The square of a finite indicator sum retains its diagonal and every ordered pair once. -/
theorem sq_sum_eq_diagonal_add_pairs {m : ℕ} (f : Fin m → ℝ) :
    (∑ i, f i)^2 = (∑ i, (f i)^2) +
      2 * ∑ i : Fin m, ∑ j : Fin m, if i.val < j.val then f i * f j else 0 := by
  have hsplit (i j : Fin m) : f i * f j =
      (if i = j then (f i)^2 else 0) +
      (if i.val < j.val then f i * f j else 0) +
      (if j.val < i.val then f i * f j else 0) := by
    rcases lt_trichotomy i.val j.val with h | h | h
    · simp only [if_pos h, if_neg (not_lt_of_ge h.le)]
      rw [if_neg (fun he => (ne_of_lt h) (congrArg Fin.val he))]
      ring
    · have he : i = j := Fin.ext h
      subst j
      simp only [↓reduceIte, lt_self_iff_false, add_zero, pow_two]
    · rw [if_neg (fun he => (ne_of_lt h) (congrArg Fin.val he).symm),
        if_neg (not_lt_of_ge h.le), if_pos h]
      ring
  have hflip : (∑ i : Fin m, ∑ j : Fin m, if j.val < i.val then f i * f j else 0) =
      ∑ i : Fin m, ∑ j : Fin m, if i.val < j.val then f i * f j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  have he : (∑ i : Fin m, ∑ j : Fin m, f i * f j) =
      ∑ i : Fin m, ∑ j : Fin m,
        ((if i = j then (f i)^2 else 0) +
          (if i.val < j.val then f i * f j else 0) +
          (if j.val < i.val then f i * f j else 0)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_congr rfl (fun j _ => hsplit i j)
  rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hflip]
  simp only [← Finset.mul_sum]
  ring

/-- Exact variance of a sum of genuine zero-one indicators under a full finite uniform law. -/
theorem uniform_indicator_variance_eq {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {m : ℕ} (I : Ω → Fin m → ℝ) (hsq : ∀ w i, (I w i)^2 = I w i) :
    let mean := (∑ w : Ω, ∑ i : Fin m, I w i) / (Fintype.card Ω : ℝ)
    (∑ w : Ω, ((∑ i : Fin m, I w i) - mean)^2) / (Fintype.card Ω : ℝ) =
      mean + 2 * (∑ i : Fin m, ∑ j : Fin m, if i.val < j.val then
        (∑ w : Ω, I w i * I w j) / (Fintype.card Ω : ℝ) else 0) - mean^2 := by
  intro mean
  let N : ℝ := Fintype.card Ω
  let Y := fun w : Ω => ∑ i : Fin m, I w i
  have hN : N ≠ 0 := by
    dsimp only [N]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Ω).ne'
  have hmean : (∑ w : Ω, Y w) = mean * N := by
    dsimp only [mean, N, Y]
    rw [div_mul_cancel₀ _ hN]
  have hcenter : (∑ w : Ω, (Y w - mean)^2) =
      (∑ w : Ω, (Y w)^2) - N * mean^2 := by
    have he (w : Ω) : (Y w - mean)^2 = (Y w)^2 - 2 * mean * Y w + mean^2 := by ring
    simp_rw [he]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hmean]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    dsimp only [N]
    ring
  have hsecond : (∑ w : Ω, (Y w)^2) = (∑ w : Ω, Y w) +
      2 * (∑ i : Fin m, ∑ j : Fin m, if i.val < j.val then
        ∑ w : Ω, I w i * I w j else 0) := by
    dsimp only [Y]
    simp_rw [sq_sum_eq_diagonal_add_pairs, hsq]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp only [Finset.sum_const_zero]
  change (∑ w : Ω, (Y w - mean)^2) / N = _
  rw [hcenter, hsecond, hmean]
  have hpairs : (∑ i : Fin m, ∑ j : Fin m, if i.val < j.val then
        (∑ w : Ω, I w i * I w j) / N else 0) =
      (∑ i : Fin m, ∑ j : Fin m, if i.val < j.val then
        ∑ w : Ω, I w i * I w j else 0) / N := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp only [zero_div]
  rw [hpairs]
  field_simp
end FiniteAvalanches.Electrical
