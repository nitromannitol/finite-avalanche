import FiniteAvalanches.Electrical.Geometry.Pendants.StraightFan
import Mathlib.Order.Filter.Finite

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.StatementGeometry.SixLeaf
open Filter Set
noncomputable section

/-- Spreading occurrences toward six fixed ranks resolves every simultaneous coincidence. -/
def leafAngle (α : Fin 6 → ℝ) (l : ℝ) (i : Fin 6) : ℝ :=
  α i+l*(α 0+2*Real.pi*((i.val:ℝ)+1)/7-α i)

theorem leafAngle_strictMono (α : Fin 6 → ℝ) (hα : Monotone α)
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1) : StrictMono (leafAngle α l) := by
  intro i j hij
  have hv : (i.val:ℝ) < j.val := by exact_mod_cast hij
  have ha := hα hij.le
  have h0 := mul_nonneg (sub_nonneg.mpr hl1.le) (sub_nonneg.mpr ha)
  have h1 := mul_pos hl0 (div_pos (mul_pos (mul_pos (by norm_num : (0:ℝ)<2) Real.pi_pos)
    (sub_pos.mpr hv)) (by norm_num : (0:ℝ)<7))
  dsimp [leafAngle]
  nlinarith only [h0,h1]

theorem leafAngle_window (α : Fin 6 → ℝ) (_hα : Monotone α)
    (hw : α 5  ≤  α 0+2*Real.pi) (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1) :
    leafAngle α l 5 < leafAngle α l 0+2*Real.pi := by
  have h0 := mul_le_mul_of_nonneg_left hw (sub_nonneg.mpr hl1.le)
  have hp := mul_pos hl0 Real.pi_pos
  dsimp [leafAngle]
  norm_num only [Fin.val_zero,show (5:Fin 6).val=5 from rfl]
  nlinarith only [h0,hp]

theorem angle_point_injective {a b : ℝ} (hlo : -2*Real.pi < b-a)
    (hhi : b-a < 2*Real.pi) (h : unitPoint a=unitPoint b) : a=b := by
  have hc : Real.cos (b-a)=1 := by
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    dsimp [unitPoint] at h1 h2
    rw [Real.cos_sub,← h1,← h2]
    simpa only [pow_two] using Real.cos_sq_add_sin_sq a
  obtain ⟨n,hn⟩ := (Real.cos_eq_one_iff (b-a)).mp hc
  have hnlo : (-1:ℝ)<n := by nlinarith only [hlo,hn,Real.pi_pos]
  have hnhi : (n:ℝ)<1 := by nlinarith only [hhi,hn,Real.pi_pos]
  have hnlo' : (-1:ℤ)<n := by exact_mod_cast hnlo
  have hnhi' : n<(1:ℤ) := by exact_mod_cast hnhi
  have hn0 : n=0 := by omega
  rw [hn0] at hn
  norm_num at hn
  linarith

theorem ordered_unitPoints_injective (θ : Fin 6 → ℝ) (hθ : StrictMono θ)
    (hw : θ 5 < θ 0+2*Real.pi) : Function.Injective (fun i => unitPoint (θ i)) := by
  intro i j h
  have hi0 := hθ.monotone (show (0:Fin 6) ≤ i by omega)
  have hj0 := hθ.monotone (show (0:Fin 6) ≤ j by omega)
  have hi5 := hθ.monotone (show i ≤ (5:Fin 6) by omega)
  have hj5 := hθ.monotone (show j ≤ (5:Fin 6) by omega)
  exact hθ.injective (angle_point_injective (by linarith) (by linarith) h)

theorem leafAngle_offset_square (α : Fin 6 → ℝ) (hα : Monotone α)
    (hw : α 5  ≤  α 0+2*Real.pi) (i : Fin 6) :
    (α 0+2*Real.pi*((i.val:ℝ)+1)/7-α i)^2  ≤  4*Real.pi^2 := by
  have h0 := hα (show (0:Fin 6) ≤ i by omega)
  have h5 := hα (show i ≤ (5:Fin 6) by omega)
  have hv0 : (0:ℝ) ≤ i.val := by positivity
  have hv5 : (i.val:ℝ) ≤ 5 := by exact_mod_cast (show i.val ≤ 5 by omega)
  have ht0 : α 0  ≤  α 0+2*Real.pi*((i.val:ℝ)+1)/7 := by nlinarith [Real.pi_pos]
  have ht5 : α 0+2*Real.pi*((i.val:ℝ)+1)/7  ≤  α 0+2*Real.pi := by
    nlinarith [Real.pi_pos]
  have hminus : 0 ≤ 2*Real.pi-(α 0+2*Real.pi*((i.val:ℝ)+1)/7-α i) := by linarith
  have hplus : 0 ≤ 2*Real.pi+(α 0+2*Real.pi*((i.val:ℝ)+1)/7-α i) := by linarith
  nlinarith only [mul_nonneg hminus hplus]

/-- Quadratic control makes every new segment initially point strictly outward. -/
theorem leafAngle_outward (α : Fin 6 → ℝ) (hα : Monotone α)
    (hw : α 5  ≤  α 0+2*Real.pi) (l : ℝ) (hl0 : 0<l)
    (hlb : l*(4*Real.pi^2+1)<1) (i : Fin 6) :
    square (scaledPoint (1-l) (unitPoint (α i))) <
      dot (scaledPoint (1-l) (unitPoint (α i))) (unitPoint (leafAngle α l i)) := by
  have hB : 0 ≤ 4*Real.pi^2 := by positivity
  have hl1 : l<1 := by nlinarith only [hlb,mul_nonneg hl0.le hB]
  have hc : 0<1-l := sub_pos.mpr hl1
  let d := α 0+2*Real.pi*((i.val:ℝ)+1)/7-α i
  have hd : d^2 ≤ 4*Real.pi^2 := leafAngle_offset_square α hα hw i
  have hmul := mul_le_mul_of_nonneg_left hd (sq_nonneg l)
  have hprod : 0<l*(2-l*(4*Real.pi^2)) :=
    mul_pos hl0 (by nlinarith only [hlb,mul_nonneg hl0.le hB])
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=l*d)
  have hnear : 1-l<Real.cos (l*d) := by
    nlinarith only [hmul,hprod,hcos]
  have hdot := mul_lt_mul_of_pos_left hnear hc
  have he : dot (scaledPoint (1-l) (unitPoint (α i))) (unitPoint (leafAngle α l i)) =
      (1-l)*Real.cos (l*d) := by
    dsimp [dot,scaledPoint,unitPoint]
    have hangle : leafAngle α l i-α i=l*d := by dsimp [leafAngle,d]; ring
    rw [← hangle,Real.cos_sub]
    ring
  rw [he]
  change (scaledPoint (1-l) (unitPoint (α i))).1^2+
    (scaledPoint (1-l) (unitPoint (α i))).2^2 < _
  rw [scaledPoint_square]
  change (1-l)^2*square (unitPoint (α i)) < _
  rw [square_unitPoint,mul_one]
  nlinarith only [hdot]

end
end FiniteAvalanches.Electrical.StatementGeometry.SixLeaf
