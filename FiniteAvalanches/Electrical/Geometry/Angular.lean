module

public import FiniteAvalanches.Electrical.Geometry.Squares
public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.Tactic.FieldSimp

/-! The actual angular test function and all pairwise oscillation estimates. -/

@[expose] public section

namespace FiniteAvalanches.Electrical.Geometry

open Set
open scoped Classical

def pointDist (z w : ℝ × ℝ) : ℝ := max |z.1-w.1| |z.2-w.2|

def radialDistance (y0 : ℝ) (z : ℝ × ℝ) : ℝ := max |z.1| |z.2-y0|

/-- The source angular test potential, on the whole real plane. -/
noncomputable def angular (epsilon y0 : ℝ) (z : ℝ × ℝ) : ℝ :=
  1/2 + (z.2-y0) / (2 * max epsilon (radialDistance y0 z))

noncomputable def Square.dilate (Q : Square) (lambda : ℝ) (hl : 0 ≤ lambda) : Square where
  x := Q.x - (lambda-1)*Q.side/2
  y := Q.y - (lambda-1)*Q.side/2
  side := lambda * Q.side
  side_nonneg := mul_nonneg hl Q.side_nonneg

theorem radialDistance_sub_le (y0 : ℝ) (z w : ℝ × ℝ) :
    |radialDistance y0 z-radialDistance y0 w| ≤ pointDist z w := by
  apply (abs_max_sub_max_le_max _ _ _ _).trans
  apply max_le_max
  · exact abs_abs_sub_abs_le _ _
  · simpa only [sub_sub_sub_cancel_right] using abs_abs_sub_abs_le (z.2-y0) (w.2-y0)

theorem denominator_sub_le (epsilon y0 : ℝ) (z w : ℝ × ℝ) :
    |max epsilon (radialDistance y0 z)-max epsilon (radialDistance y0 w)| ≤ pointDist z w := by
  rw [max_comm epsilon, max_comm epsilon]
  exact (abs_max_sub_max_le_abs _ _ _).trans (radialDistance_sub_le y0 z w)

theorem ratio_sub_le (n m D E t : ℝ) (hD : 0 < D) (hE : 0 < E)
    (hnm : |n-m| ≤ t) (hm : |m| ≤ E) (hDE : |D-E| ≤ t) :
    |n/(2*D)-m/(2*E)| ≤ t/D := by
  have heq : n/(2*D)-m/(2*E) = ((n-m)*E+m*(E-D))/(2*D*E) := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos (by positivity : 0 < 2*D*E)]
  apply (div_le_iff₀ (by positivity : 0 < 2*D*E)).mpr
  calc
    _ ≤ |n-m| *E + |m| *|E-D| := by
      simpa only [abs_mul, abs_of_pos hE] using abs_add_le ((n-m)*E) (m*(E-D))
    _ ≤ t*E+E*t := add_le_add (mul_le_mul_of_nonneg_right hnm hE.le)
      (mul_le_mul hm (by simpa only [abs_sub_comm] using hDE) (abs_nonneg _) hE.le)
    _ = t/D*(2*D*E) := by field_simp; ring

theorem angular_sub_le (epsilon y0 : ℝ) (he : 0 < epsilon) (z w : ℝ × ℝ) :
    |angular epsilon y0 z-angular epsilon y0 w| ≤
      pointDist z w / max epsilon (radialDistance y0 z) := by
  unfold angular
  rw [add_sub_add_left_eq_sub]
  apply ratio_sub_le
  · exact he.trans_le (le_max_left _ _)
  · exact he.trans_le (le_max_left _ _)
  · change |(z.2-y0)-(w.2-y0)| ≤ max |z.1-w.1| |z.2-w.2|
    rw [sub_sub_sub_cancel_right]
    exact le_max_right _ _
  · exact (le_max_right _ _).trans (le_max_right _ _)
  · exact denominator_sub_le epsilon y0 z w

theorem angular_mem_unitInterval (epsilon y0 : ℝ) (he : 0 < epsilon) (z : ℝ × ℝ) :
    0 ≤ angular epsilon y0 z ∧ angular epsilon y0 z ≤ 1 := by
  have hD : 0 < max epsilon (radialDistance y0 z) := he.trans_le (le_max_left _ _)
  have hn : |z.2-y0| ≤ max epsilon (radialDistance y0 z) :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hn' := abs_le.mp hn
  unfold angular
  constructor
  · have h := (le_div_iff₀ (by positivity : 0 < 2*max epsilon (radialDistance y0 z))).mpr
      (show (-1/2 : ℝ)*(2*max epsilon (radialDistance y0 z)) ≤ z.2-y0 by linarith [hn'.1])
    linarith only [h]
  · have h := (div_le_iff₀ (by positivity : 0 < 2*max epsilon (radialDistance y0 z))).mpr
      (show z.2-y0 ≤ (1/2 : ℝ)*(2*max epsilon (radialDistance y0 z)) by linarith [hn'.2])
    linarith only [h]

theorem angular_sub_le_one (epsilon y0 : ℝ) (he : 0 < epsilon) (z w : ℝ × ℝ) :
    |angular epsilon y0 z-angular epsilon y0 w| ≤ 1 := by
  have hz := angular_mem_unitInterval epsilon y0 he z
  have hw := angular_mem_unitInterval epsilon y0 he w
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem pointDist_le_of_mem_square (Q : Square) (z w : ℝ × ℝ)
    (hz : z ∈ Q.carrier) (hw : w ∈ Q.carrier) : pointDist z w ≤ Q.side := by
  apply max_le
  · exact abs_le.mpr ⟨by linarith [hz.1.1, hw.1.2], by linarith [hz.1.2, hw.1.1]⟩
  · exact abs_le.mpr ⟨by linarith [hz.2.1, hw.2.2], by linarith [hz.2.2, hw.2.1]⟩

theorem corner_distance_le (Q : Square) (lambda : ℝ) (hl : 1 ≤ lambda)
    (z : ℝ × ℝ) (hz : z ∈ (Q.dilate lambda (by linarith)).carrier) :
    pointDist (Q.x,Q.y) z ≤ lambda*Q.side := by
  have hn := Q.side_nonneg
  have hs : 0 ≤ (lambda-1)*Q.side := mul_nonneg (by linarith) hn
  apply max_le
  · exact abs_le.mpr ⟨by dsimp [Square.dilate] at hz; linarith [hz.1.2],
      by dsimp [Square.dilate] at hz; linarith [hz.1.1]⟩
  · exact abs_le.mpr ⟨by dsimp [Square.dilate] at hz; linarith [hz.2.2],
      by dsimp [Square.dilate] at hz; linarith [hz.2.1]⟩

/-- Each pair in a dilated square satisfies the scale estimate, including zero-side squares. -/
theorem angular_sub_le_scale (Q : Square) (epsilon y0 lambda : ℝ) (he : 0 < epsilon)
    (hl : 1 ≤ lambda) (z w : ℝ × ℝ)
    (hz : z ∈ (Q.dilate lambda (by linarith)).carrier)
    (hw : w ∈ (Q.dilate lambda (by linarith)).carrier) :
    |angular epsilon y0 z-angular epsilon y0 w| ≤
      4*lambda^2*Q.side/Q.scale epsilon y0 := by
  let r := Q.scale epsilon y0
  let D := max epsilon (radialDistance y0 z)
  have hr : 0 < r := he.trans_le (Q.scale_bounds epsilon y0).1
  have hD : 0 < D := he.trans_le (le_max_left _ _)
  have hdiam := pointDist_le_of_mem_square (Q.dilate lambda (by linarith)) z w hz hw
  change pointDist z w ≤ lambda*Q.side at hdiam
  have hlocal := angular_sub_le epsilon y0 he z w
  change |angular epsilon y0 z-angular epsilon y0 w| ≤ pointDist z w/D at hlocal
  have hc := corner_distance_le Q lambda hl z hz
  have hrad := radialDistance_sub_le y0 (Q.x,Q.y) z
  have hcorner : radialDistance y0 (Q.x,Q.y) ≤ D+lambda*Q.side := by
    have hh := (le_abs_self _).trans (hrad.trans hc)
    have hrd : radialDistance y0 z ≤ D := le_max_right _ _
    linarith only [hh, hrd]
  by_cases hsmall : r ≤ 2*lambda*Q.side
  · have h1 := angular_sub_le_one epsilon y0 he z w
    apply h1.trans
    apply (le_div_iff₀ hr).mpr
    have hs := Q.side_nonneg
    have hh : 2*lambda ≤ 4*lambda^2 := by nlinarith only [hl]
    have hm := mul_le_mul_of_nonneg_right hh hs
    linarith only [hsmall, hm]
  · have hrD : r ≤ 2*D := by
      have hcase : epsilon = r ∨ Q.side = r ∨ radialDistance y0 (Q.x,Q.y) = r := by
        dsimp [r, Square.scale, radialDistance]
        rcases le_total epsilon (max Q.side (max |Q.x| |Q.y-y0|)) with h | h
        · rw [max_eq_right h]
          rcases le_total Q.side (max |Q.x| |Q.y-y0|) with h | h
          · exact Or.inr (Or.inr (max_eq_right h).symm)
          · exact Or.inr (Or.inl (max_eq_left h).symm)
        · exact Or.inl (max_eq_left h).symm
      rcases hcase with h | h | h
      · have hd : epsilon ≤ D := le_max_left _ _
        linarith only [h, hd, hD]
      · exfalso
        have hs' := Q.side_nonneg
        nlinarith only [h, hsmall, hl, hs']
      · have hh := hcorner
        rw [h] at hh
        have hs' := (lt_of_not_ge hsmall)
        linarith only [hh, hs']
    calc
      _ ≤ lambda*Q.side/D := hlocal.trans (div_le_div_of_nonneg_right hdiam hD.le)
      _ ≤ 4*lambda^2*Q.side/r := by
        apply (div_le_div_iff₀ hD hr).mpr
        have hs := Q.side_nonneg
        have hh : 2*lambda ≤ 4*lambda^2 := by nlinarith only [hl]
        have h1 := mul_le_mul_of_nonneg_left hrD (mul_nonneg (by linarith : 0 ≤ lambda) hs)
        have h2 := mul_le_mul_of_nonneg_right hh (mul_nonneg hs hD.le)
        nlinarith only [h1, h2]

end FiniteAvalanches.Electrical.Geometry
