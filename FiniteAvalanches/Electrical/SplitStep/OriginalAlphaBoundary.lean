import FiniteAvalanches.Electrical.SplitStep.OriginalMarkedCharts

set_option autoImplicit false

namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing
open scoped Classical BigOperators
noncomputable section

/-- The literal alpha indicator has nonzero gradient precisely on the complete alpha star. -/
theorem alpha_indicator_gradient {V E : Type} [DecidableEq V] (J : CopiedGraph V E)
    (hloop : ∀ e, J.left e ≠ J.right e) (alpha : V) (e : E) :
    let g := Plane.copyGradient J.left J.right (fun x => if x = alpha then (1 : ℝ) else 0) e
    (J.left e = alpha → g = 1) ∧
    (J.right e = alpha → g = -1) ∧
    (¬(J.left e = alpha ∨ J.right e = alpha) → g = 0) := by
  intro g
  refine ⟨?_, ?_, ?_⟩
  · intro ha
    have hb : J.right e ≠ alpha := fun hb => hloop e (ha.trans hb.symm)
    simp only [g, Plane.copyGradient, if_pos ha, if_neg hb, sub_zero]
  · intro hb
    have ha : J.left e ≠ alpha := fun ha => hloop e (ha.trans hb.symm)
    simp only [g, Plane.copyGradient, if_neg ha, if_pos hb, zero_sub]
  · intro hn
    simp only [not_or] at hn
    simp only [g, Plane.copyGradient, if_neg hn.1, if_neg hn.2, sub_self]

/-- The original full-H face boundary is exactly the supplied complete star path plus marked ID. -/
theorem original_alpha_boundary_sum (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q : Drawing (LatticeDrawing.primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) {m : ℕ}
    (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) (F : Face Q) :
    let J := sourceDualGraph D P Q charts
    let K := LatticeDrawing.primalGraph D P
    let g := Plane.copyGradient K.left K.right (fun x => if x = alpha D P then (1 : ℝ) else 0)
    Plane.copyBoundary J.left J.right g F =
      (∑ k : Fin m,
        ((if J.left (retainedPrimal D P marked (copies k).val) = F then
          g (retainedPrimal D P marked (copies k).val) else 0) -
        (if J.right (retainedPrimal D P marked (copies k).val) = F then
          g (retainedPrimal D P marked (copies k).val) else 0))) +
      ((if J.left (markedPrimal D P marked) = F then g (markedPrimal D P marked) else 0) -
        (if J.right (markedPrimal D P marked) = F then g (markedPrimal D P marked) else 0)) := by
  intro J K g
  let f : LatticeDrawing.PrimalCopy D P → ℝ := fun e =>
    (if J.left e = F then g e else 0) - (if J.right e = F then g e else 0)
  have hz (e : Copy D P marked)
      (he : ¬(copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P)) :
      f (retainedPrimal D P marked e) = 0 := by
    have hg : g (retainedPrimal D P marked e) = 0 := by
      simpa only [g, K] using (alpha_indicator_gradient (LatticeDrawing.primalGraph D P)
        (primal_loopless D P) (alpha D P) (retainedPrimal D P marked e)).2.2 he
    simp only [f, hg, ite_self, sub_self]
  have hsum : (∑ e : Copy D P marked, f (retainedPrimal D P marked e)) =
      ∑ k : Fin m, f (retainedPrimal D P marked (copies k).val) := by
    have h := Finset.sum_congr_set
      {e : Copy D P marked | copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}
      (fun e => f (retainedPrimal D P marked e))
      (fun e => f (retainedPrimal D P marked e.val)) (fun _ _ => rfl) hz
    rw [h]
    exact (copies.sum_comp (fun e => f (retainedPrimal D P marked e.val))).symm
  change (∑ e, f e) = _
  rw [← (augmentedOriginalCopyEquiv D P marked).sum_comp f]
  simp only [Fintype.sum_sum_type, Fintype.sum_unique]
  change (∑ e : Copy D P marked, f (retainedPrimal D P marked e)) +
    f (markedPrimal D P marked) = _
  rw [hsum]

/-- The coefficient of a supplied unoriented path copy when followed in its listed order. -/
def pathFlowCoefficient {W : Type} {m : ℕ} (a : Fin m → W)
    (vertices : Fin (m + 1) → W) (g : Fin m → ℝ) (k : Fin m) : ℝ :=
  if a k = vertices k.castSucc then g k else -g k

theorem path_boundary_internal {W : Type} {m : ℕ} (a b : Fin m → W)
    (vertices : Fin (m + 1) → W) (hinj : Function.Injective vertices)
    (hends : ∀ k, (a k = vertices k.castSucc ∧ b k = vertices k.succ) ∨
      (b k = vertices k.castSucc ∧ a k = vertices k.succ))
    (g : Fin m → ℝ) (k : Fin m) (hk : k.val + 1 < m) :
    Plane.copyBoundary a b g (vertices k.succ) =
      pathFlowCoefficient a vertices g ⟨k.val + 1, hk⟩ - pathFlowCoefficient a vertices g k := by
  let c := pathFlowCoefficient a vertices g
  have ht (j : Fin m) (F : W) :
      ((if a j = F then g j else 0) - (if b j = F then g j else 0)) =
      ((if vertices j.castSucc = F then c j else 0) -
        (if vertices j.succ = F then c j else 0)) := by
    have hne : vertices j.succ ≠ vertices j.castSucc := by
      intro he
      have hv := congrArg Fin.val (hinj he)
      simp only [Fin.val_succ, Fin.val_castSucc] at hv
      omega
    rcases hends j with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · simp only [c, pathFlowCoefficient, ha, hb, ↓reduceIte]
    · simp only [c, pathFlowCoefficient, ha, if_neg hne, hb]
      split_ifs <;> ring
  have hleft (j : Fin m) : vertices j.castSucc = vertices k.succ ↔ j = ⟨k.val + 1, hk⟩ := by
    constructor
    · intro he
      have hv := congrArg Fin.val (hinj he)
      exact Fin.ext hv
    · intro he
      subst j
      congr 1
  have hright (j : Fin m) : vertices j.succ = vertices k.succ ↔ j = k := by
    constructor
    · intro he
      have hv := congrArg Fin.val (hinj he)
      simp only [Fin.val_succ] at hv
      apply Fin.ext
      omega
    · rintro rfl; rfl
  simp only [Plane.copyBoundary, ht, hleft, hright, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

end
end FiniteAvalanches.Electrical.SplitStep
