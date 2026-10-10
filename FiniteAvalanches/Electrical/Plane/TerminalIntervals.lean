import FiniteAvalanches.Electrical.Plane.TerminalOrder
import FiniteAvalanches.Electrical.Plane.TerminalIncidence

/-! Exact cumulative intervals for an integrated stream on the actual face quotient.
This file characterizes that stream; it does not assert its existence. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped BigOperators Classical
open FiniteAvalanches.Electrical.Geometry

/-- Actual ordered alpha currents; the physical outgoing current is their negative. -/
noncomputable def alphaCurrentSequence {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (phi : V → ℝ) :
    Fin (incidenceCount a b alpha) → ℝ :=
  fun i => phi (head a b (alphaEnumeration R alpha beta hne da db ha hb i).val)

theorem alpha_stream_prefix {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (phi : V → ℝ) (hphi : phi alpha = 0)
    (psi : ArcFace R da db → ℝ)
    (hpsi : ∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) =
      arcCurrent a b phi (energy a b phi) d)
    (h0 : psi (arcRightFace R da db (.inr false)) = 0) :
    ∀ n : ℕ, n ≤ incidenceCount a b alpha →
      psi (arcLeftFace R da db (((insertArcRotation R da db)^(n+1)) (.inr false))) =
        boundaryHeight (alphaCurrentSequence R alpha beta hne da db ha hb phi) n := by
  let s := alphaCurrentSequence R alpha beta hne da db ha hb phi
  intro n
  induction n with
  | zero =>
    intro _
    simp only [Nat.zero_add,pow_one,arcLeftFace_next,h0,boundaryHeight,
      Nat.not_lt_zero,if_false,Finset.sum_const_zero]
  | succ n ih =>
    intro hn
    have hnLt : n < incidenceCount a b alpha := by omega
    let i : Fin (incidenceCount a b alpha) := ⟨n,hnLt⟩
    have h := alpha_stream_step R da db phi psi alpha hphi
      (alphaEnumeration R alpha beta hne da db ha hb i).val
      (alphaEnumeration R alpha beta hne da db ha hb i).property
      (hpsi (.inl (alphaEnumeration R alpha beta hne da db ha hb i).val))
    rw [alphaEnumeration_spec] at h
    change psi (arcLeftFace R da db (insertArcRotation R da db
        (((insertArcRotation R da db)^(n+1)) (.inr false))))-
      psi (arcLeftFace R da db (((insertArcRotation R da db)^(n+1)) (.inr false))) = s i at h
    have hh := boundaryHeight_succ s i
    have hi := ih (by omega)
    rw [pow_succ',Equiv.Perm.mul_apply]
    change _ = boundaryHeight s (n+1)
    change boundaryHeight s (n+1) = boundaryHeight s n+s i at hh
    linarith only [h,hh,hi]

/-- Every enumerated incidence has precisely its cumulative interval, not just orbit coverage. -/
theorem alpha_stream_interval {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (phi : V → ℝ) (hphi : phi alpha = 0)
    (psi : ArcFace R da db → ℝ)
    (hpsi : ∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) =
      arcCurrent a b phi (energy a b phi) d)
    (h0 : psi (arcRightFace R da db (.inr false)) = 0) (i : Fin (incidenceCount a b alpha)) :
    psi (arcLeftFace R da db (.inl (alphaEnumeration R alpha beta hne da db ha hb i).val)) =
        boundaryHeight (alphaCurrentSequence R alpha beta hne da db ha hb phi) i.val ∧
    psi (arcRightFace R da db (.inl (alphaEnumeration R alpha beta hne da db ha hb i).val)) =
        boundaryHeight (alphaCurrentSequence R alpha beta hne da db ha hb phi) i.val+
          alphaCurrentSequence R alpha beta hne da db ha hb phi i := by
  have hl := alpha_stream_prefix R alpha beta hne da db ha hb phi hphi psi hpsi h0 i.val i.isLt.le
  rw [← alphaEnumeration_spec R alpha beta hne da db ha hb i] at hl
  have h := hpsi (.inl (alphaEnumeration R alpha beta hne da db ha hb i).val)
  change _ = current a b phi (alphaEnumeration R alpha beta hne da db ha hb i).val at h
  unfold current at h
  rw [(alphaEnumeration R alpha beta hne da db ha hb i).property,hphi] at h
  exact ⟨hl,by dsimp [alphaCurrentSequence]; linarith only [hl,h]⟩

/-- The ordered original current sum is derived from the actual arc jump and first return. -/
theorem sum_alphaCurrentSequence_eq_energy {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (phi : V → ℝ) (hphi : phi alpha = 0)
    (psi : ArcFace R da db → ℝ)
    (hpsi : ∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) =
      arcCurrent a b phi (energy a b phi) d)
    (h0 : psi (arcRightFace R da db (.inr false)) = 0) :
    (∑ i, alphaCurrentSequence R alpha beta hne da db ha hb phi i) = energy a b phi := by
  have h := alpha_stream_prefix R alpha beta hne da db ha hb phi hphi psi hpsi h0
    (incidenceCount a b alpha) le_rfl
  rw [(alpha_first_return R alpha beta hne da db ha hb).1] at h
  have hu := exterior_stream_values R da db phi psi (energy a b phi) (hpsi (.inr false)) h0
  rw [hu] at h
  simp only [boundaryHeight,Fin.isLt,if_true] at h
  exact h.symm

end FiniteAvalanches.Electrical.Plane
