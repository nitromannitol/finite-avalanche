import FiniteAvalanches.Electrical.Geometry.Pendants.ScaledDrawing
import FiniteAvalanches.Electrical.Geometry.BoundaryOrder
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.StatementGeometry.SixLeaf
noncomputable section

def square (p : ℝ × ℝ) : ℝ := p.1^2+p.2^2
def dot (p q : ℝ × ℝ) : ℝ := p.1*q.1+p.2*q.2
def unitPoint (a : ℝ) : ℝ × ℝ := (Real.cos a,Real.sin a)
def segment (a b : ℝ × ℝ) (t : ℝ) : ℝ × ℝ := (1-t) • a+t • b

theorem square_nonneg (p : ℝ × ℝ) : 0 ≤ square p := add_nonneg (sq_nonneg _) (sq_nonneg _)
theorem square_unitPoint (a : ℝ) : square (unitPoint a)=1 := Real.cos_sq_add_sin_sq a

theorem segment_square (a b : ℝ × ℝ) (t : ℝ) :
    square (segment a b t) = (1-t)*square a+t*square b-t*(1-t)*square (b-a) := by
  dsimp [square,segment]
  ring

theorem segment_square_outward (a b : ℝ × ℝ) (t : ℝ) :
    square (segment a b t) = square a+2*t*(dot a b-square a)+t^2*square (b-a) := by
  dsimp [square,segment,dot]
  ring

theorem segment_disk (a b : ℝ × ℝ) (ha : square a ≤ 1) (hb : square b ≤ 1)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : square (segment a b t) ≤ 1 := by
  rw [segment_square]
  have h0 := mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr ht1)
  have h1 := mul_le_mul_of_nonneg_left hb ht0
  have h2 := mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht1)) (square_nonneg (b-a))
  nlinarith only [h0,h1,h2]

theorem segment_strict_disk (a b : ℝ × ℝ) (ha : square a < 1) (hb : square b = 1)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) : square (segment a b t) < 1 := by
  rw [segment_square,hb]
  have h0 := mul_lt_mul_of_pos_left ha (sub_pos.mpr ht1)
  have h2 := mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht1.le)) (square_nonneg (b-a))
  nlinarith only [h0,h2]

theorem segment_outside (a b : ℝ × ℝ) (hab : square a < dot a b)
    (t : ℝ) (ht : 0 < t) : square a < square (segment a b t) := by
  rw [segment_square_outward]
  have h1 := mul_pos ht (sub_pos.mpr hab)
  have h2 := mul_nonneg (sq_nonneg t) (square_nonneg (b-a))
  nlinarith only [h1,h2]

theorem segment_injective (a b : ℝ × ℝ) (hab : a ≠ b) : Function.Injective (segment a b) := by
  intro s t h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  dsimp [segment] at h1 h2
  by_cases hf : a.1 = b.1
  · have hs : a.2 ≠ b.2 := fun hs => hab (Prod.ext hf hs)
    have he : (s-t)*(a.2-b.2)=0 := by nlinarith only [h2]
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hs))
  · have he : (s-t)*(a.1-b.1)=0 := by nlinarith only [h1]
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hf))

/-- Two distinct boundary rays from an interior point meet only at the common attachment. -/
theorem same_attachment_intersection (a b d : ℝ × ℝ)
    (ha : square a < 1) (hb : square b=1) (hd : square d=1) (hbd : b ≠ d)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (h : segment a b s = segment a d t) : s=0 ∧ t=0 := by
  have hab : a ≠ b := fun h => by rw [h,hb] at ha; exact (lt_irrefl _ ha)
  have had : a ≠ d := fun h => by rw [h,hd] at ha; exact (lt_irrefl _ ha)
  by_cases hs0 : s=0
  · refine ⟨hs0,?_⟩
    have he : segment a d 0 = segment a d t := by simpa [hs0,segment] using h
    exact (segment_injective a d had he).symm
  by_cases ht0 : t=0
  · have he : segment a b s = segment a b 0 := by simpa [ht0,segment] using h
    exact (hs0 (segment_injective a b hab he)).elim
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  let p := segment a b s-a
  have hp : p = segment a d t-a := congrArg (fun z => z-a) h
  have hbq : s^2*(1-square a)=2*s*dot a p+square p := by
    dsimp [p,square,dot,segment]
    dsimp [square] at hb
    nlinarith only [hb]
  have hdq : t^2*(1-square a)=2*t*dot a p+square p := by
    rw [hp]
    dsimp [square,dot,segment]
    dsimp [square] at hd
    nlinarith only [hd]
  have hfactor : (s-t)*(s*t*(1-square a)+square p)=0 := by
    have he := congrArg (fun z => t*z) hbq
    have hf := congrArg (fun z => s*z) hdq
    nlinarith only [he,hf]
  have hpositive : 0 < s*t*(1-square a)+square p :=
    add_pos_of_pos_of_nonneg (mul_pos (mul_pos hspos htpos) (sub_pos.mpr ha)) (square_nonneg p)
  have hst : s=t := sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right (ne_of_gt hpositive))
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  rw [hst] at h1 h2
  dsimp [segment] at h1 h2
  have hbd' : b=d := by
    apply Prod.ext
    · exact mul_left_cancel₀ (ne_of_gt htpos) (by nlinarith only [h1] : t*b.1=t*d.1)
    · exact mul_left_cancel₀ (ne_of_gt htpos) (by nlinarith only [h2] : t*b.2=t*d.2)
  exact (hbd hbd').elim

end
end FiniteAvalanches.Electrical.StatementGeometry.SixLeaf
