import FiniteAvalanches.Electrical.Geometry.PhysicalCharging
import FiniteAvalanches.Electrical.SplitStep.SignedAngularOscillation

/-! Signed midpoint trials on the unchanged physical squares and copied split graph. -/

namespace FiniteAvalanches.Electrical.PhysicalCharging
open StatementGeometry Plane Geometry SplitStep
open scoped Classical BigOperators
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

/-- Physical free midpoints use the numerical sign; beta stays zero and alpha stays zero/one. -/
def signedSplitMidpointTrial (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (alpha beta : V) (A : Source.OuterArc D alpha beta)
    (phi : V → ℝ) (psi : A.embedding.Face → ℝ) (sigma epsilon y0 : ℝ) :
    SplitVertex alpha → ℝ
  | .inl x => if x.val = beta then 0 else
      signedAngular sigma epsilon y0 (segmentMidpoint J D alpha beta A phi psi x.val)
  | .inr k => if k then 1 else 0

lemma signedSplitMidpointTrial_one (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (alpha beta : V) (A : Source.OuterArc D alpha beta)
    (phi : V → ℝ) (psi : A.embedding.Face → ℝ) (epsilon y0 : ℝ) :
    signedSplitMidpointTrial J D alpha beta A phi psi 1 epsilon y0 =
      splitMidpointTrial J D alpha beta A phi psi epsilon y0 := by
  funext v
  cases v with
  | inl x => simp only [signedSplitMidpointTrial, splitMidpointTrial, signed_angular_eq_angular]
  | inr k => rfl

lemma signedSplitMidpointTrial_mem_unitInterval (J : CopiedGraph V E)
    (D : Source.PlaneEmbedding J) (alpha beta : V) (A : Source.OuterArc D alpha beta)
    (phi : V → ℝ) (psi : A.embedding.Face → ℝ) (sigma epsilon y0 : ℝ)
    (hsigma : sigma = 1 ∨ sigma = -1) (he : 0 < epsilon) (v : SplitVertex alpha) :
    0 ≤ signedSplitMidpointTrial J D alpha beta A phi psi sigma epsilon y0 v ∧
      signedSplitMidpointTrial J D alpha beta A phi psi sigma epsilon y0 v ≤ 1 := by
  cases v with
  | inl x =>
    dsimp only [signedSplitMidpointTrial]
    split_ifs
    · norm_num
    · have h := angular_mem_unitInterval epsilon y0 he
        (segmentMidpoint J D alpha beta A phi psi x.val)
      rcases hsigma with rfl | rfl
      · rw [signed_angular_eq_angular]; exact h
      · rw [signed_angular_neg_eq_one_sub]; constructor <;> linarith only [h.1, h.2]
  | inr k => cases k <;> norm_num [signedSplitMidpointTrial]

/-- Complementing free values requires reversing the alpha side; beta is excluded here. -/
lemma signed_minus_endpoint_eq_one_sub (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (alpha beta : V) (A : Source.OuterArc D alpha beta)
    (phi : V → ℝ) (psi : A.embedding.Face → ℝ) (side : E → Bool)
    (epsilon y0 : ℝ) (x : V) (e : E) (hx : x ≠ beta) :
    signedSplitMidpointTrial J D alpha beta A phi psi (-1) epsilon y0
        (splitEndpoint alpha side x e) =
      1 - splitMidpointTrial J D alpha beta A phi psi epsilon y0
        (splitEndpoint alpha (fun e => !(side e)) x e) := by
  by_cases ha : x = alpha
  · subst x
    cases hs : side e <;> simp [splitEndpoint, signedSplitMidpointTrial, splitMidpointTrial, hs]
  · simp only [splitEndpoint, dif_neg ha, signedSplitMidpointTrial, splitMidpointTrial,
      if_neg hx, signed_angular_neg_eq_one_sub]

/-- Literal weighted-copy equality: beta remains zero in both trials and has actual zero weight. -/
lemma signed_minus_weighted_copy_eq (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (alpha beta : V) (A : Source.OuterArc D alpha beta)
    (phi : V → ℝ) (psi : A.embedding.Face → ℝ) (hbeta : phi beta = 1)
    (side : E → Bool) (epsilon y0 : ℝ) (e : E) :
    let f := signedSplitMidpointTrial J D alpha beta A phi psi (-1) epsilon y0
    let g := splitMidpointTrial J D alpha beta A phi psi epsilon y0
    (1 - phi (J.left e)) * (1 - phi (J.right e)) *
        (f (splitEndpoint alpha side (J.left e) e) -
          f (splitEndpoint alpha side (J.right e) e)) ^ 2 =
      (1 - phi (J.left e)) * (1 - phi (J.right e)) *
        (g (splitEndpoint alpha (fun e => !(side e)) (J.left e) e) -
          g (splitEndpoint alpha (fun e => !(side e)) (J.right e) e)) ^ 2 := by
  intro f g
  by_cases ha : J.left e = beta
  · rw [ha, hbeta, sub_self, zero_mul, zero_mul, zero_mul]
  by_cases hb : J.right e = beta
  · rw [hb, hbeta, sub_self, mul_zero, zero_mul, zero_mul]
  have hl := signed_minus_endpoint_eq_one_sub J D alpha beta A phi psi side epsilon y0 (J.left e) e ha
  have hr := signed_minus_endpoint_eq_one_sub J D alpha beta A phi psi side epsilon y0 (J.right e) e hb
  dsimp only [f, g]
  rw [hl, hr]
  ring

/-- Both signs have exact charge27 on the same squares. The signed terminal heights
remain an ordinary conditional geometric predecessor. -/
theorem physical_signed_split_charging_of_terminal_heights
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (hne : alpha ≠ beta) (A : Source.OuterArc D alpha beta)
    (psi : A.embedding.Face → ℝ)
    (hpsi : Source.stream_spec D alpha beta A (Source.voltage J alpha beta hc) psi)
    (hdeg : ∀ x, x ≠ alpha → x ≠ beta → degree J.left J.right x ≤ 4)
    (side : E → Bool) (exception : E) (sigma epsilon y0 : ℝ)
    (hsigma : sigma = 1 ∨ sigma = -1) (he : 0 < epsilon)
    (hheight : ∀ e, e ≠ exception → J.left e = alpha ∨ J.right e = alpha →
      if side e then epsilon ≤ sigma *
        ((copySquare J D alpha beta A (Source.voltage J alpha beta hc) psi e).y +
          (copySquare J D alpha beta A (Source.voltage J alpha beta hc) psi e).side / 2 - y0)
      else sigma *
        ((copySquare J D alpha beta A (Source.voltage J alpha beta hc) psi e).y +
          (copySquare J D alpha beta A (Source.voltage J alpha beta hc) psi e).side / 2 - y0) ≤ -epsilon) :
    let phi := Source.voltage J alpha beta hc
    let Q := copySquare J D alpha beta A phi psi
    let a := fun e => splitEndpoint alpha side (J.left e) e
    let b := fun e => splitEndpoint alpha side (J.right e) e
    let f := signedSplitMidpointTrial J D alpha beta A phi psi sigma epsilon y0
    let weight := fun v => 1 - phi (collapse alpha v)
    (∑ e, weight (a e) * weight (b e) * (f (a e) - f (b e)) ^ 2) ≤
      1 + 27 * ∑ e, ((Q e).angularOsc epsilon y0 3 (by norm_num) he) ^ 2 := by
  rcases hsigma with rfl | rfl
  · have hh : ∀ e, e ≠ exception → J.left e = alpha ∨ J.right e = alpha →
        if side e then y0 + epsilon ≤
          (copySquare J D alpha beta A (Source.voltage J alpha beta hc) psi e).y +
            (copySquare J D alpha beta A (Source.voltage J alpha beta hc) psi e).side / 2
        else (copySquare J D alpha beta A (Source.voltage J alpha beta hc) psi e).y +
            (copySquare J D alpha beta A (Source.voltage J alpha beta hc) psi e).side / 2 ≤ y0 - epsilon := by
      intro e hex hi
      have h := hheight e hex hi
      cases hs : side e <;> simp only [hs, Bool.false_eq_true, if_false, if_true, one_mul] at h ⊢ <;>
        linarith only [h]
    simpa only [signedSplitMidpointTrial_one] using
      physical_split_charging_of_terminal_heights J D hc alpha beta hne A psi hpsi hdeg
        side exception epsilon y0 he hh
  · have hh : ∀ e, e ≠ exception → J.left e = alpha ∨ J.right e = alpha →
        if !(side e) then y0 + epsilon ≤
          (copySquare J D alpha beta A (Source.voltage J alpha beta hc) psi e).y +
            (copySquare J D alpha beta A (Source.voltage J alpha beta hc) psi e).side / 2
        else (copySquare J D alpha beta A (Source.voltage J alpha beta hc) psi e).y +
            (copySquare J D alpha beta A (Source.voltage J alpha beta hc) psi e).side / 2 ≤ y0 - epsilon := by
      intro e hex hi
      have h := hheight e hex hi
      cases hs : side e <;> simp only [hs, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        if_false, if_true, neg_one_mul] at h ⊢ <;> linarith only [h]
    have h := physical_split_charging_of_terminal_heights J D hc alpha beta hne A psi hpsi hdeg
      (fun e => !(side e)) exception epsilon y0 he hh
    dsimp only at h ⊢
    simp only [collapse_splitEndpoint] at h ⊢
    have hb := (Source.voltage_spec J alpha beta hne hc).2.1
    have heq := fun e => signed_minus_weighted_copy_eq J D alpha beta A
      (Source.voltage J alpha beta hc) psi hb side epsilon y0 e
    simp_rw [heq]
    exact h

end
end FiniteAvalanches.Electrical.PhysicalCharging
