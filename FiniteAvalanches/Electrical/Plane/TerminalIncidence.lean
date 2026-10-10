import FiniteAvalanches.Electrical.Plane.ArcCycles
import FiniteAvalanches.Electrical.Plane.Squares

/-! Terminal orbit coverage and exact endpoint stream values, conditional on integration. -/
namespace FiniteAvalanches.Electrical.Plane

open scoped Classical

/-- The actual augmented rotation reaches every original alpha incidence. -/
theorem exists_alpha_orbit_index {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (d : Dart E)
    (hd : tail a b d = alpha) :
    ∃ n : ℕ, ((insertArcRotation R da db)^n) (.inr false) = .inl d := by
  apply Equiv.Perm.SameCycle.exists_nat_pow_eq
  apply (insertArcRotation_sameCycle_iff R alpha beta hne da db ha hb _ _).mpr
  exact hd.symm

/-- Every alpha edge has its actual stream increase equal to its voltage/current magnitude. -/
theorem alpha_stream_step {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ)
    (psi : ArcFace R da db → ℝ) (alpha : V) (hphi : phi alpha = 0) (d : Dart E)
    (hd : tail a b d = alpha)
    (h : psi (arcLeftFace R da db (.inl d))-psi (arcRightFace R da db (.inl d)) = current a b phi d) :
    psi (arcLeftFace R da db (insertArcRotation R da db (.inl d)))-
      psi (arcLeftFace R da db (.inl d)) = phi (head a b d) := by
  rw [arcLeftFace_next]
  unfold current at h
  rw [hd,hphi] at h
  linarith only [h]

/-- The last original alpha incidence ends exactly at the M exterior face. -/
theorem last_alpha_stream_eq_energy {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ)
    (psi : ArcFace R da db → ℝ)
    (h : psi (arcLeftFace R da db (.inr false))-psi (arcRightFace R da db (.inr false)) =
      arcCurrent a b phi (energy a b phi) (.inr false))
    (h0 : psi (arcRightFace R da db (.inr false)) = 0) :
    psi (arcRightFace R da db (.inl da)) = energy a b phi := by
  have hl := arcLeftFace_next R da db (.inl da)
  rw [insertArcRotation_alpha] at hl
  rw [← hl]
  exact exterior_stream_values R da db phi psi (energy a b phi) h h0

end FiniteAvalanches.Electrical.Plane
