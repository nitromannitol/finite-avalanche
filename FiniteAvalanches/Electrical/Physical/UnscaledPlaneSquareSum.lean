import FiniteAvalanches.Electrical.Physical.UnscaledSquareSum
import FiniteAvalanches.Electrical.Plane.AngularEnergy

/-! Sharp 144 on the actual once-indexed electrical square family. -/

open Set
open scoped BigOperators Classical
open FiniteAvalanches.Electrical.Geometry
open FiniteAvalanches.Electrical.Physical.Unscaled

namespace FiniteAvalanches.Electrical.Plane

/-- The existing electrical current identities and normalized voltage produce both geometric inputs.
The sum retains every original copy ID, including parallel copies and zero-current points. -/
theorem actual_angular_square_sum_le_144 {V E : Type*} [Fintype V] [Fintype E]
    {a b : E → V} (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta)
    (da db : Dart E) (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (hc : (supportGraph a b).Preconnected) (phi : V → ℝ)
    (hpa : phi alpha = 0) (hpb : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ z, psi (arcLeftFace R da db z) - psi (arcRightFace R da db z) =
      arcCurrent a b phi (energy a b phi) z)
    (h0 : psi (arcRightFace R da db (.inr false)) = 0)
    (epsilon y0 : ℝ) (he : 0 < epsilon) (he1 : epsilon ≤ 1) :
    (∑ e : E, ((incrementSquare R da db phi psi (e, false) (hp (.inl (e, false)))).angularOsc
      epsilon y0 3 (by norm_num) he) ^ 2) ≤ 144 * (1 + Real.log (1 / epsilon)) := by
  let Q := fun e : E => incrementSquare R da db phi psi (e, false) (hp (.inl (e, false)))
  have hd := square_open_disjoint R alpha beta hne da db ha hb hc phi hpa hpb hh
    (energy a b phi) psi hp
  have hQ : ∀ e ∈ (Finset.univ : Finset E),
      (Q e).carrier ⊆ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ) := by
    intro e _ z hz
    have hrect := incrementSquare_subset_rectangle R alpha beta hne da db ha hb
      hc phi hpa hpb hh psi hp h0 (e, false) hz
    exact ⟨hrect.1, mem_univ z.2⟩
  exact angular_square_sum_le_144 Finset.univ Q hd epsilon y0 he he1 hQ

/-- For any supplied positive original alpha copy, its literal p/2 cutoff yields log(2/p).
The upper bound p≤1 is derived from unit-voltage square containment. -/
theorem actual_alpha_cutoff_square_sum_le_144 {V E : Type*} [Fintype V] [Fintype E]
    {a b : E → V} (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta)
    (da db : Dart E) (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (hc : (supportGraph a b).Preconnected) (phi : V → ℝ)
    (hpa : phi alpha = 0) (hpb : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ z, psi (arcLeftFace R da db z) - psi (arcRightFace R da db z) =
      arcCurrent a b phi (energy a b phi) z)
    (h0 : psi (arcRightFace R da db (.inr false)) = 0)
    (j : Fin (incidenceCount a b alpha))
    (hpj : 0 < alphaCurrentSequence R alpha beta hne da db ha hb phi j) (y0 : ℝ) :
    let p := alphaCurrentSequence R alpha beta hne da db ha hb phi j
    (∑ e : E, ((incrementSquare R da db phi psi (e, false) (hp (.inl (e, false)))).angularOsc
      (p / 2) y0 3 (by norm_num) (by positivity)) ^ 2) ≤
        144 * (1 + Real.log (2 / p)) := by
  intro p
  have hp1 : p ≤ 1 := by
    dsimp only [p]
    rw [alpha_current_eq_square_side R alpha beta hne da db ha hb phi hpa psi hp j hpj.le]
    exact (Square.side_le_min_of_subset _ _
      (incrementSquare_subset_rectangle R alpha beta hne da db ha hb hc phi hpa hpb hh psi hp h0 _)).trans
      (min_le_left _ _)
  have he : 0 < p / 2 := by positivity
  have he1 : p / 2 ≤ 1 := by linarith only [hp1]
  have hrecip : 1 / (p / 2) = 2 / p := by ring
  simpa only [hrecip] using actual_angular_square_sum_le_144 R alpha beta hne da db ha hb
    hc phi hpa hpb hh psi hp h0 (p / 2) y0 he he1

end FiniteAvalanches.Electrical.Plane
