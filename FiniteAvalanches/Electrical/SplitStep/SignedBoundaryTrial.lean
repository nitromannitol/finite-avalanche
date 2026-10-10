import FiniteAvalanches.Electrical.Geometry.SignedPhysicalEnergy
import FiniteAvalanches.Electrical.SplitStep.OrderedBoundary

/-! Derive both adjacent-copy terminal heights from actual physical boundary-step data. -/
namespace FiniteAvalanches.Electrical.PhysicalCharging
open StatementGeometry Plane Geometry SplitStep ChordSplit
open scoped Classical BigOperators
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

private lemma min_add_half_abs_sub (a b : ℝ) : min a b + |a - b| / 2 = (a + b) / 2 := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring

/-- The physical alpha-side midpoint is the average of the two actual incident stream heights. -/
lemma copySquare_midpoint_eq (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (alpha beta : V) (A : Source.OuterArc D alpha beta)
    (phi : V → ℝ) (psi : A.embedding.Face → ℝ)
    (hpsi : Source.stream_spec D alpha beta A phi psi) (e : E) :
    (copySquare J D alpha beta A phi psi e).y +
        (copySquare J D alpha beta A phi psi e).side / 2 =
      (psi (A.embedding.leftFace (.inl e)) + psi (A.embedding.rightFace (.inl e))) / 2 := by
  change min _ _ + |phi (J.left e) - phi (J.right e)| / 2 = _
  rw [← hpsi.1 e, min_add_half_abs_sub]

/-- Once the actual full alpha-copy order and its coherent signed increments are supplied,
both adjacent choices give the sharp trial bound on this same physical carrier. -/
theorem physical_signed_trial_le_3888_of_boundary_steps
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (hne : alpha ≠ beta) (A : Source.OuterArc D alpha beta)
    (psi : A.embedding.Face → ℝ)
    (hpsi : Source.stream_spec D alpha beta A (Source.voltage J alpha beta hc) psi)
    (hdeg : ∀ x, x ≠ alpha → x ≠ beta → degree J.left J.right x ≤ 4)
    {m : ℕ} (vertices : Fin (m + 1) → A.embedding.Face)
    (copies : Fin m ≃ {e : E // J.left e = alpha ∨ J.right e = alpha})
    (hends : ∀ k : Fin m,
      (A.embedding.leftFace (.inl (copies k).val) = vertices k.castSucc ∧
        A.embedding.rightFace (.inl (copies k).val) = vertices k.succ) ∨
      (A.embedding.rightFace (.inl (copies k).val) = vertices k.castSucc ∧
        A.embedding.leftFace (.inl (copies k).val) = vertices k.succ))
    (sigma : ℝ) (hsigma : sigma = 1 ∨ sigma = -1)
    (hstep : ∀ k : Fin m,
      sigma * (psi (vertices k.succ) - psi (vertices k.castSucc)) =
        |Source.voltage J alpha beta hc (J.left (copies k).val) -
          Source.voltage J alpha beta hc (J.right (copies k).val)|)
    (i : Fin (m + 1)) (j : Fin m) (hj : j.val + 1 = i.val ∨ j.val = i.val)
    (hpj : 0 < |Source.voltage J alpha beta hc (J.left (copies j).val) -
      Source.voltage J alpha beta hc (J.right (copies j).val)|) :
    let phi := Source.voltage J alpha beta hc
    let p := |phi (J.left (copies j).val) - phi (J.right (copies j).val)|
    let y0 := (psi (vertices j.castSucc) + psi (vertices j.succ)) / 2
    let K := splitGraph J alpha (boundarySide J.left J.right alpha copies i.val)
    let f := signedSplitMidpointTrial J D alpha beta A phi psi sigma (p / 2) y0
    f (.inr false) = 0 ∧ f (.inr true) = 1 ∧
      f (.inl ⟨beta, hne.symm⟩) = 0 ∧ (∀ v, 0 ≤ f v ∧ f v ≤ 1) ∧
      weightedEnergy K.left K.right (fun v => 1 - phi (collapse alpha v)) f ≤
        1 + 3888 * (1 + Real.log (2 / p)) := by
  intro phi p y0 K f
  have hbound := signed_trial_boundary_and_range J D alpha beta hne A phi psi
    sigma (p / 2) y0 hsigma (by positivity)
  refine ⟨hbound.1, hbound.2.1, hbound.2.2.1, hbound.2.2.2, ?_⟩
  apply physical_signed_trial_le_3888_of_terminal_heights J D hc alpha beta hne A psi hpsi hdeg
    (boundarySide J.left J.right alpha copies i.val) (copies j).val sigma y0 hsigma hpj
  intro e hex hi
  let k : Fin m := copies.symm ⟨e, hi⟩
  have he : (copies k).val = e := congrArg Subtype.val (copies.apply_symm_apply ⟨e, hi⟩)
  have hkj : k ≠ j := fun h => hex (he.symm.trans (congrArg (fun r => (copies r).val) h))
  let currents := fun k : Fin m => |phi (J.left (copies k).val) - phi (J.right (copies k).val)|
  have hm : (copySquare J D alpha beta A phi psi e).y +
      (copySquare J D alpha beta A phi psi e).side / 2 =
      (psi (vertices k.castSucc) + psi (vertices k.succ)) / 2 := by
    rw [← he, copySquare_midpoint_eq J D alpha beta A phi psi hpsi]
    rcases hends k with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · rw [hl, hr]
    · rw [hl, hr, add_comm]
  have hmid := signed_terminal_midpoint_bounds (fun r => psi (vertices r)) currents
    (fun k => abs_nonneg _) sigma hstep i j hj k hkj
  have hs : boundarySide J.left J.right alpha copies i.val e = decide (i.val ≤ k.val) := by
    rw [← he, boundarySide_copy]
  dsimp only
  rw [hm, hs]
  by_cases hik : i.val ≤ k.val
  · rw [decide_eq_true hik, if_pos rfl]
    exact hmid.2 hik
  · rw [decide_eq_false hik, if_neg Bool.false_ne_true]
    exact hmid.1 (lt_of_not_ge hik)

end
end FiniteAvalanches.Electrical.PhysicalCharging
