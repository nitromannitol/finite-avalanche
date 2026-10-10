import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit false
namespace JointFiniteProbability
open scoped Classical BigOperators
noncomputable section

/-- Finite Paley--Zygmund with the whole original sample denominator. -/
theorem paley_zygmund_quarter {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (M B : ℝ) (hM : 0 < M) (hB : 0 < B)
    (hX : ∀ x, 0 ≤ X x)
    (hmean : M / 2 ≤ (∑ x, X x) / (Fintype.card Ω : ℝ))
    (hsecond : (∑ x, (X x)^2) / (Fintype.card Ω : ℝ) ≤ B * M^2) :
    1 / (16 * B) ≤
      ((Finset.univ.filter (fun x => M / 4 ≤ X x)).card : ℝ) /
        (Fintype.card Ω : ℝ) := by
  let S := Finset.univ.filter (fun x => M / 4 ≤ X x)
  let T := Finset.univ.filter (fun x => ¬M / 4 ≤ X x)
  have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hs0 : 0 ≤ ∑ x ∈ S, X x := Finset.sum_nonneg fun x _ => hX x
  have hbad : (∑ x ∈ T, X x) ≤ (Fintype.card Ω : ℝ) * (M / 4) := by
    calc
      _ ≤ ∑ _x ∈ T, M / 4 := Finset.sum_le_sum fun x hx =>
        le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hx).2)
      _ = (T.card : ℝ) * (M / 4) := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Fintype.card Ω : ℝ) * (M / 4) :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _)))
          (by positivity)
  have hsplit : (∑ x ∈ S, X x) + (∑ x ∈ T, X x) = ∑ x, X x :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have htotal := (le_div_iff₀ hN).mp hmean
  have hs : (Fintype.card Ω : ℝ) * M / 4 ≤ ∑ x ∈ S, X x := by
    linarith only [hbad, hsplit, htotal]
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq S X (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcauchy
  have hsq : (∑ x ∈ S, (X x)^2) ≤ ∑ x, (X x)^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun x _ _ => sq_nonneg (X x))
  have hsecond' := (div_le_iff₀ hN).mp hsecond
  have hcard : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hh : ((Fintype.card Ω : ℝ) * M / 4)^2 ≤
      (S.card : ℝ) * (B * M^2 * (Fintype.card Ω : ℝ)) := by
    calc
      _ ≤ (∑ x ∈ S, X x)^2 := sq_le_sq₀ (by positivity) hs0 |>.mpr hs
      _ ≤ (∑ x ∈ S, (X x)^2) * (S.card : ℝ) := hcauchy
      _ ≤ (B * M^2 * (Fintype.card Ω : ℝ)) * (S.card : ℝ) :=
        mul_le_mul_of_nonneg_right (hsq.trans hsecond') hcard
      _ = _ := mul_comm _ _
  have hfactor : 0 < (Fintype.card Ω : ℝ) * M^2 := mul_pos hN (sq_pos_of_pos hM)
  have hfinal : (Fintype.card Ω : ℝ) ≤ 16 * B * (S.card : ℝ) := by
    nlinarith only [hh, hfactor]
  change 1 / (16 * B) ≤ (S.card : ℝ) / (Fintype.card Ω : ℝ)
  apply (div_le_div_iff₀ (by positivity : 0 < 16 * B) hN).mpr
  nlinarith only [hfinal]

theorem second_moment_eq_variance_add_sq {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) :
    (∑ x, (X x)^2) / (Fintype.card Ω : ℝ) =
      (∑ x, (X x - (∑ y, X y) / (Fintype.card Ω : ℝ))^2) /
        (Fintype.card Ω : ℝ) + ((∑ x, X x) / (Fintype.card Ω : ℝ))^2 := by
  have hn : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt Fintype.card_pos
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  field_simp
  ring

end
end JointFiniteProbability
