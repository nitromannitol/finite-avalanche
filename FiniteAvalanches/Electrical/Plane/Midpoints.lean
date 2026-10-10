import FiniteAvalanches.Electrical.Plane.SplitTrial

/-! Actual within-copy midpoint comparison, including the zero-current common point. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical
open FiniteAvalanches.Electrical.Geometry

/-- The midpoint at the head is the midpoint of the reversed original incidence. -/
theorem sideMidpoint_reverse {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ) (psi : ArcFace R da db → ℝ)
    (z : Dart E) : sideMidpoint R da db phi psi (reverse E z) =
      (phi (head a b z),(psi (arcLeftFace R da db (.inl z))+psi (arcRightFace R da db (.inl z)))/2) := by
  have hl : arcLeftFace R da db (.inl (reverse E z)) = arcRightFace R da db (.inl z) := rfl
  have hr : arcRightFace R da db (.inl (reverse E z)) = arcLeftFace R da db (.inl z) := by
    change arcLeftFace R da db (arcReverse E (arcReverse E (.inl z))) = _
    rw [arcReverse_arcReverse]
  simp only [sideMidpoint,tail_reverse,hl,hr,add_comm]

/-- Every original copy retains its own middle oscillation term in the canonical comparison. -/
theorem actual_middle_error_le {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ) (psi : ArcFace R da db → ℝ)
    (M : ℝ) (hp : ∀ z, psi (arcLeftFace R da db z)-psi (arcRightFace R da db z) = arcCurrent a b phi M z)
    (epsilon y0 lambda : ℝ) (he : 0 < epsilon) (hl : 1 ≤ lambda) (e : E) :
    |angular epsilon y0 (sideMidpoint R da db phi psi (e,false))-
      angular epsilon y0 (sideMidpoint R da db phi psi (e,true))| ≤
        (incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))).angularOsc epsilon y0 lambda hl he := by
  rw [show (e,true) = reverse E (e,false) from rfl,sideMidpoint_reverse]
  exact midpoint_middle_error_le R da db phi psi (e,false) (hp (.inl (e,false))) epsilon y0 lambda he hl

/-- A true zero-current original copy contributes exactly zero middle error and zero dilated oscillation. -/
theorem actual_zero_middle_error {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ) (psi : ArcFace R da db → ℝ)
    (M : ℝ) (hp : ∀ z, psi (arcLeftFace R da db z)-psi (arcRightFace R da db z) = arcCurrent a b phi M z)
    (epsilon y0 lambda : ℝ) (he : 0 < epsilon) (hl : 1 ≤ lambda) (e : E)
    (hz : current a b phi (e,false) = 0) :
    angular epsilon y0 (sideMidpoint R da db phi psi (e,false)) =
      angular epsilon y0 (sideMidpoint R da db phi psi (e,true)) ∧
    (incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))).angularOsc epsilon y0 lambda hl he = 0 := by
  have hside := (incrementSquare_zero_current R da db phi psi (e,false) (hp (.inl (e,false))) hz).1
  have hosc := Square.angularOsc_eq_zero_of_side_eq_zero _ epsilon y0 lambda he hl hside
  have herr := actual_middle_error_le R da db phi psi M hp epsilon y0 lambda he hl e
  rw [hosc] at herr
  exact ⟨sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm herr (abs_nonneg _))),hosc⟩

end FiniteAvalanches.Electrical.Plane
