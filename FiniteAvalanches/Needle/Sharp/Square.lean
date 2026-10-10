import FiniteAvalanches.Needle.Sharp.Edges

set_option autoImplicit false
namespace Needle107Square
open LatticeProb FiniteAvalanches.Needle FiniteAvalanches.Sandpile.FiniteWired
open scoped BigOperators Classical

noncomputable def tent (r : ℕ) (R : ℤ) : ℝ :=
  min 1 (max 0 ((R : ℝ) - r) / r)

lemma tent_zero (r : ℕ) (R : ℤ) (hR : R ≤ r) : tent r R = 0 := by
  have hc : (R : ℝ) ≤ r := by exact_mod_cast hR
  rw [tent, max_eq_left (by linarith only [hc]), zero_div]
  norm_num

lemma tent_one (r : ℕ) (hr : 1 ≤ r) (R : ℤ) (hR : 2*r ≤ R) : tent r R = 1 := by
  have hc : 2*(r : ℝ) ≤ R := by exact_mod_cast hR
  have hp : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  rw [tent, min_eq_left]
  apply (le_div_iff₀ hp).mpr
  exact (by linarith only [hc] : 1*(r : ℝ) ≤ (R : ℝ)-r).trans (le_max_right _ _)

lemma tent_lipschitz (r : ℕ) (hr : 1 ≤ r) (R S : ℤ) (hRS : |R-S| ≤ 1) :
    |tent r R - tent r S| ≤ 1/(r : ℝ) := by
  have hp : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hh : |(R : ℝ) - S| ≤ 1 := by exact_mod_cast hRS
  have hmin := abs_min_sub_min_le_max (1 : ℝ) (max 0 ((R : ℝ)-r)/r)
    1 (max 0 ((S : ℝ)-r)/r)
  have hmax := abs_max_sub_max_le_max (0 : ℝ) ((R : ℝ)-r) 0 ((S : ℝ)-r)
  rw [sub_self, abs_zero, max_eq_right (a := (0 : ℝ))
    (b := |max 0 ((R : ℝ)-r)/r-max 0 ((S : ℝ)-r)/r|) (abs_nonneg _)] at hmin
  rw [sub_self, abs_zero, max_eq_right (a := (0 : ℝ))
    (b := |((R : ℝ)-r)-((S : ℝ)-r)|) (abs_nonneg _), sub_sub_sub_cancel_right] at hmax
  have hv : |max 0 ((R : ℝ)-r)/r - max 0 ((S : ℝ)-r)/r| ≤ 1/r := by
    rw [← sub_div, abs_div, abs_of_pos hp]
    apply (div_le_div_iff_of_pos_right hp).mpr
    exact hmax.trans hh
  exact hmin.trans hv

lemma tent_max_core (r : ℕ) (a b : ℤ) (ha : |a| ≤ r) :
    tent r (max |a| |b|) = tent r |b| := by
  by_cases hb : |b| ≤ r
  · rw [tent_zero r _ (max_le ha hb), tent_zero r _ hb]
  · rw [max_eq_right (by omega)]

noncomputable def band (r : ℕ) : Finset ℤ :=
  Finset.Icc (r : ℤ) (2*r-1) ∪ Finset.Icc (-(2*(r : ℤ))) (-(r : ℤ)-1)

lemma tent_changed_band (r : ℕ) (hr : 1 ≤ r) (a b : ℤ)
    (hne : tent r (max |a| |b|) ≠ tent r (max |a+1| |b|)) :
    a ∈ band r ∧ b ∈ Finset.Icc (-(2*(r : ℤ))+1) (2*r-1) := by
  constructor
  · by_contra ha
    simp only [band, Finset.mem_union, Finset.mem_Icc, not_or, not_and_or] at ha
    have hcases : a < -(2*(r : ℤ)) ∨ 2*(r : ℤ) ≤ a ∨
        (|a| ≤ r ∧ |a+1| ≤ r) := by
      simp only [abs_le]
      omega
    rcases hcases with ht | ht | ⟨hc, hd⟩
    · have hc : 2*(r : ℤ) ≤ max |a| |b| := by
        exact (by omega : 2*(r : ℤ) ≤ -a).trans ((neg_le_abs a).trans (le_max_left _ _))
      have hd : 2*(r : ℤ) ≤ max |a+1| |b| := by
        exact (by omega : 2*(r : ℤ) ≤ -(a+1)).trans ((neg_le_abs (a+1)).trans (le_max_left _ _))
      exact hne ((tent_one r hr _ hc).trans (tent_one r hr _ hd).symm)
    · have hc : 2*(r : ℤ) ≤ max |a| |b| := ht.trans ((le_abs_self a).trans (le_max_left _ _))
      have hd : 2*(r : ℤ) ≤ max |a+1| |b| := by
        have := (le_abs_self (a+1)).trans (le_max_left |a+1| |b|); omega
      exact hne ((tent_one r hr _ hc).trans (tent_one r hr _ hd).symm)
    · exact hne ((tent_max_core r a b hc).trans (tent_max_core r (a+1) b hd).symm)
  · apply Finset.mem_Icc.mpr
    by_contra hb
    have hc : 2*(r : ℤ) ≤ |b| := by rw [abs_eq_max_neg]; omega
    exact hne ((tent_one r hr _ (hc.trans (le_max_right _ _))).trans
      (tent_one r hr _ (hc.trans (le_max_right _ _))).symm)

lemma card_band (r : ℕ) (hr : 1 ≤ r) : (band r).card ≤ 2*r := by
  have h1 : (Finset.Icc (r : ℤ) (2*r-1)).card = r := by rw [Int.card_Icc]; omega
  have h2 : (Finset.Icc (-(2*(r : ℤ))) (-(r : ℤ)-1)).card = r := by rw [Int.card_Icc]; omega
  exact (Finset.card_union_le _ _).trans (by rw [h1, h2]; omega)

noncomputable def window (r : ℕ) (c : Point) : Finset (Point × Fin 2) :=
  ((band r ×ˢ Finset.Icc (-(2*(r : ℤ))+1) (2*r-1)).image
    (fun q => (![c 0 + q.1, c 1 + q.2], (0 : Fin 2)))) ∪
  ((band r ×ˢ Finset.Icc (-(2*(r : ℤ))+1) (2*r-1)).image
    (fun q => (![c 0 + q.2, c 1 + q.1], (1 : Fin 2))))

lemma card_window (r : ℕ) (hr : 1 ≤ r) (c : Point) :
    (window r c).card ≤ 16*r*r := by
  have hc : (Finset.Icc (-(2*(r : ℤ))+1) (2*r-1)).card = 4*r-1 := by
    rw [Int.card_Icc]; omega
  have hp : (band r ×ˢ Finset.Icc (-(2*(r : ℤ))+1) (2*r-1)).card ≤
      2*r*(4*r-1) := by
    rw [Finset.card_product, hc]
    exact Nat.mul_le_mul_right _ (card_band r hr)
  refine (Finset.card_union_le _ _).trans ?_
  have h1 := (Finset.card_image_le (s := band r ×ˢ
    Finset.Icc (-(2*(r : ℤ))+1) (2*r-1))
    (f := fun q : ℤ × ℤ => (![c 0 + q.1, c 1 + q.2], (0 : Fin 2)))).trans hp
  have h2 := (Finset.card_image_le (s := band r ×ˢ
    Finset.Icc (-(2*(r : ℤ))+1) (2*r-1))
    (f := fun q : ℤ × ℤ => (![c 0 + q.2, c 1 + q.1], (1 : Fin 2)))).trans hp
  have hm : 2*r*(4*r-1) ≤ 8*r*r := by
    calc _ ≤ 2*r*(4*r) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
         _ = _ := by ring
  have heq : 8*r*r+8*r*r = 16*r*r := by ring
  exact (Nat.add_le_add (h1.trans hm) (h2.trans hm)).trans heq.le

lemma changed_mem_window (r : ℕ) (hr : 1 ≤ r) (c x : Point) (i : Fin 2)
    (hne : tent r (radius (x-c)) ≠ tent r (radius (x+unit i-c))) :
    (x, i) ∈ window r c := by
  have hx : ![x 0, x 1] = x := by funext j; fin_cases j <;> rfl
  fin_cases i
  · have h0 : (x+unit (0 : Fin 2)-c) 0 = x 0-c 0+1 := by simp [unit]; ring
    have h1 : (x+unit (0 : Fin 2)-c) 1 = x 1-c 1 := by simp [unit]
    change tent r (max |x 0-c 0| |x 1-c 1|) ≠
      tent r (max |(x+unit (0 : Fin 2)-c) 0| |(x+unit (0 : Fin 2)-c) 1|) at hne
    rw [h0, h1] at hne
    have hh := tent_changed_band r hr (x 0-c 0) (x 1-c 1) hne
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨(x 0-c 0, x 1-c 1), Finset.mem_product.mpr hh, ?_⟩
    congr 1
    simpa only [add_sub_cancel] using hx
  · have h0 : (x+unit (1 : Fin 2)-c) 0 = x 0-c 0 := by simp [unit]
    have h1 : (x+unit (1 : Fin 2)-c) 1 = x 1-c 1+1 := by simp [unit]; ring
    change tent r (max |x 0-c 0| |x 1-c 1|) ≠
      tent r (max |(x+unit (1 : Fin 2)-c) 0| |(x+unit (1 : Fin 2)-c) 1|) at hne
    rw [h0, h1] at hne
    have hh := tent_changed_band r hr (x 1-c 1) (x 0-c 0) (by
      simpa only [max_comm] using hne)
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨(x 1-c 1, x 0-c 0), Finset.mem_product.mpr hh, ?_⟩
    congr 1
    simpa only [add_sub_cancel] using hx

end Needle107Square
