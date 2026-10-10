import FiniteAvalanches.Electrical.Geometry.SignedPhysicalCharging
import FiniteAvalanches.Electrical.Physical.UnscaledPhysicalSquareSum
import FiniteAvalanches.Electrical.Energy
import FiniteAvalanches.Electrical.ChordSplit.CopiedDiagram

/-! Sharp energy from charge27 and sum144 on the identical original physical carrier. -/
namespace FiniteAvalanches.Electrical.PhysicalCharging
open StatementGeometry Plane Geometry SplitStep ChordSplit
open scoped Classical BigOperators
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

/-- The two existing numerical converters are literally the same closed physical square. -/
lemma copySquare_eq_physicalSquare (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (alpha beta : V) (A : Source.OuterArc D alpha beta)
    (phi : V → ℝ) (psi : A.embedding.Face → ℝ) (e : E) :
    copySquare J D alpha beta A phi psi e =
      Physical.Unscaled.physicalSquare J D alpha beta A phi psi e := rfl

/-- The sharp cutoff sum on the charging theorem's identical original copies and squares. -/
theorem copySquare_cutoff_square_sum_le_144 (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected) (alpha beta : V) (hne : alpha ≠ beta)
    (A : Source.OuterArc D alpha beta) (psi : A.embedding.Face → ℝ)
    (hpsi : Source.stream_spec D alpha beta A (Source.voltage J alpha beta hc) psi)
    (j : E) (hpj : 0 < |Source.voltage J alpha beta hc (J.left j) -
      Source.voltage J alpha beta hc (J.right j)|) (y0 : ℝ) :
    let p := |Source.voltage J alpha beta hc (J.left j) - Source.voltage J alpha beta hc (J.right j)|
    (∑ e : E, ((copySquare J D alpha beta A (Source.voltage J alpha beta hc) psi e).angularOsc
      (p / 2) y0 3 (by norm_num) (by positivity)) ^ 2) ≤
        144 * (1 + Real.log (2 / p)) := by
  intro p
  simp only [copySquare_eq_physicalSquare]
  exact Physical.Unscaled.physical_copy_cutoff_square_sum_le_144
    J D hc alpha beta hne A psi hpsi j hpj y0

/-- The signed trial has alpha values zero/one, beta zero, and range [0,1]. -/
theorem signed_trial_boundary_and_range (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (alpha beta : V) (hne : alpha ≠ beta) (A : Source.OuterArc D alpha beta)
    (phi : V → ℝ) (psi : A.embedding.Face → ℝ) (sigma epsilon y0 : ℝ)
    (hsigma : sigma = 1 ∨ sigma = -1) (he : 0 < epsilon) :
    let f := signedSplitMidpointTrial J D alpha beta A phi psi sigma epsilon y0
    f (.inr false) = 0 ∧ f (.inr true) = 1 ∧
      f (.inl ⟨beta, hne.symm⟩) = 0 ∧ ∀ v, 0 ≤ f v ∧ f v ≤ 1 := by
  intro f
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp only [f, signedSplitMidpointTrial, if_true]
  · exact signedSplitMidpointTrial_mem_unitInterval J D alpha beta A phi psi sigma epsilon y0 hsigma he

/-- Actual weighted split energy at the selected copy's p/2, for either numerical sign.
Only the explicitly named terminal-height predecessor is conditional. -/
theorem physical_signed_trial_le_3888_of_terminal_heights
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (hne : alpha ≠ beta) (A : Source.OuterArc D alpha beta)
    (psi : A.embedding.Face → ℝ)
    (hpsi : Source.stream_spec D alpha beta A (Source.voltage J alpha beta hc) psi)
    (hdeg : ∀ x, x ≠ alpha → x ≠ beta → degree J.left J.right x ≤ 4)
    (side : E → Bool) (j : E) (sigma y0 : ℝ) (hsigma : sigma = 1 ∨ sigma = -1)
    (hpj : 0 < |Source.voltage J alpha beta hc (J.left j) -
      Source.voltage J alpha beta hc (J.right j)|)
    (hheight : ∀ e, e ≠ j → J.left e = alpha ∨ J.right e = alpha →
      let p := |Source.voltage J alpha beta hc (J.left j) - Source.voltage J alpha beta hc (J.right j)|
      if side e then p / 2 ≤ sigma *
        ((copySquare J D alpha beta A (Source.voltage J alpha beta hc) psi e).y +
          (copySquare J D alpha beta A (Source.voltage J alpha beta hc) psi e).side / 2 - y0)
      else sigma *
        ((copySquare J D alpha beta A (Source.voltage J alpha beta hc) psi e).y +
          (copySquare J D alpha beta A (Source.voltage J alpha beta hc) psi e).side / 2 - y0) ≤ -(p / 2)) :
    let phi := Source.voltage J alpha beta hc
    let p := |phi (J.left j) - phi (J.right j)|
    let K := splitGraph J alpha side
    let f := signedSplitMidpointTrial J D alpha beta A phi psi sigma (p / 2) y0
    weightedEnergy K.left K.right (fun v => 1 - phi (collapse alpha v)) f ≤
      1 + 3888 * (1 + Real.log (2 / p)) := by
  intro phi p K f
  have hcharge := physical_signed_split_charging_of_terminal_heights
    J D hc alpha beta hne A psi hpsi hdeg side j sigma (p / 2) y0 hsigma (by positivity) hheight
  have hsum := copySquare_cutoff_square_sum_le_144 J D hc alpha beta hne A psi hpsi j hpj y0
  change (∑ e, (1 - phi (collapse alpha (K.left e))) * (1 - phi (collapse alpha (K.right e))) *
      (f (K.left e) - f (K.right e)) ^ 2) ≤ _
  calc
    _ ≤ 1 + 27 * ∑ e, ((copySquare J D alpha beta A phi psi e).angularOsc
        (p / 2) y0 3 (by norm_num) (by positivity)) ^ 2 := hcharge
    _ ≤ 1 + 27 * (144 * (1 + Real.log (2 / p))) :=
      add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left hsum (by norm_num))
    _ = _ := by ring

end
end FiniteAvalanches.Electrical.PhysicalCharging
