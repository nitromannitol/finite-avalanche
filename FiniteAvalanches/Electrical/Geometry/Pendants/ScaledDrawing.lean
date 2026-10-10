import FiniteAvalanches.Electrical.Geometry.DiskDrawing
import Mathlib.Tactic

/-! Actual uniform scaling of every vertex and every original copied curve. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.StatementGeometry
noncomputable section

def scaledPoint (c : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (c*p.1,c*p.2)

theorem scaledPoint_injective (c : ℝ) (hc : c ≠ 0) : Function.Injective (scaledPoint c) := by
  intro p q h
  apply Prod.ext
  · exact mul_left_cancel₀ hc (congrArg Prod.fst h)
  · exact mul_left_cancel₀ hc (congrArg Prod.snd h)

theorem scaledPoint_square (c : ℝ) (p : ℝ × ℝ) :
    (scaledPoint c p).1^2+(scaledPoint c p).2^2 = c^2*(p.1^2+p.2^2) := by
  dsimp [scaledPoint]
  ring

/-- A strict uniform contraction sends every old boundary vertex strictly inside. -/
theorem scaledPoint_not_circle (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (p : ℝ × ℝ) (hp : p ∈ circle) : scaledPoint c p ∉ circle := by
  change p.1^2+p.2^2=1 at hp
  intro hs
  change (scaledPoint c p).1^2+(scaledPoint c p).2^2=1 at hs
  rw [scaledPoint_square,hp,mul_one] at hs
  have hh := mul_lt_mul_of_pos_left hc1 hc0
  nlinarith only [hh,hc1,hs]

namespace Drawing
variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- All full Drawing obligations survive, including original loops and parallel IDs. -/
def rescale (D : Drawing J) (c : ℝ) (hc : c ≠ 0) : Drawing J where
  point := scaledPoint c ∘ D.point
  point_injective := (scaledPoint_injective c hc).comp D.point_injective
  curve := fun e t => scaledPoint c (D.curve e t)
  continuous := by
    intro e
    exact (continuous_const.mul (D.continuous e).fst).prodMk
      (continuous_const.mul (D.continuous e).snd)
  injective := by
    intro e s hs t ht h
    exact D.injective e hs ht (scaledPoint_injective c hc h)
  start := by
    intro e
    change scaledPoint c (D.curve e _) = scaledPoint c (D.point (J.left e))
    rw [D.start]
  finish := by
    intro e
    change scaledPoint c (D.curve e _) = scaledPoint c (D.point (J.right e))
    rw [D.finish]
  avoids := by
    intro e t ht0 ht1 v h
    exact D.avoids e t ht0 ht1 v (scaledPoint_injective c hc h)
  intersects := by
    intro e f hef s t h
    exact D.intersects e f hef s t (scaledPoint_injective c hc h)

theorem rescale_original_curve (D : Drawing J) (c : ℝ) (hc : c ≠ 0) (e : E) (t : ArcParameter) :
    (D.rescale c hc).curve e t = scaledPoint c (D.curve e t) := rfl

/-- Containment in the smaller squared-radius disk holds for every unchanged original copy. -/
theorem rescale_curve_disk (D : Drawing J) (c : ℝ) (hc : c ≠ 0)
    (hD : ∀ e t, D.curve e t ∈ disk) (e : E) (t : ArcParameter) :
    ((D.rescale c hc).curve e t).1^2+((D.rescale c hc).curve e t).2^2 ≤ c^2 := by
  change (scaledPoint c (D.curve e t)).1^2+(scaledPoint c (D.curve e t)).2^2 ≤ c^2
  rw [scaledPoint_square]
  have h := mul_le_mul_of_nonneg_left (hD e t) (sq_nonneg c)
  simpa only [mul_one] using h

end Drawing
end
end FiniteAvalanches.Electrical.StatementGeometry
