import FiniteAvalanches.Electrical.SplitStep.OriginalStreamBalance
import FiniteAvalanches.Electrical.SplitStep.BoundaryPositive

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Electrical.Source.CurrentTerminalHeight
open LatticeProb StatementGeometry BSST Plane.SourceLattice LatticeDrawing SplitStep
open scoped Classical BigOperators
noncomputable section

/-- Split the full copied face boundary into all retained original IDs and its unique
marked ID. No alpha-star restriction or simple-edge quotient is used. -/
theorem full_boundary_eq_retained_add_marked
    (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)
    (Q : Drawing (LatticeDrawing.primalGraph D P)) (charts : ∀ e, EdgeChart Q e)
    (phi : Vertex D P → ℝ) (F : Face Q) :
    let K := LatticeDrawing.primalGraph D P
    let J := sourceDualGraph D P Q charts
    let R := sourceDeletedDualGraph D P marked Q charts
    let g := Plane.copyGradient K.left K.right phi
    Plane.copyBoundary J.left J.right g F =
      Plane.copyBoundary R.left R.right
        (fun e => phi (copyA D P marked e) - phi (copyB D P marked e)) F +
      ((if J.left (markedPrimal D P marked) = F then g (markedPrimal D P marked) else 0) -
       (if J.right (markedPrimal D P marked) = F then g (markedPrimal D P marked) else 0)) := by
  intro K J R g
  let f : LatticeDrawing.PrimalCopy D P → ℝ := fun e =>
    (if J.left e = F then g e else 0) - (if J.right e = F then g e else 0)
  change (∑ e, f e) = _
  rw [← (augmentedOriginalCopyEquiv D P marked).sum_comp f]
  simp only [Fintype.sum_sum_type, Fintype.sum_unique]
  rfl

/-- The integrated physical stream has exactly the residual carried by the deleted
marked copy. Universal face balance is used at the actual source voltage. -/
theorem stream_laplacian_eq_marked_residual
    (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)
    (Q : Drawing (LatticeDrawing.primalGraph D P)) (charts : ∀ e, EdgeChart Q e)
    (phi : Vertex D P → ℝ) (eta : Face Q → ℝ)
    (hstream : ∀ e : Copy D P marked,
      eta ((sourceDeletedDualGraph D P marked Q charts).right e) -
        eta ((sourceDeletedDualGraph D P marked Q charts).left e) =
      phi (copyA D P marked e) - phi (copyB D P marked e))
    (hbalance : ∀ F : Face Q,
      Plane.copyBoundary (sourceDualGraph D P Q charts).left
        (sourceDualGraph D P Q charts).right
        (Plane.copyGradient (LatticeDrawing.primalGraph D P).left (LatticeDrawing.primalGraph D P).right phi) F = 0)
    (F : Face Q) :
    let J := sourceDualGraph D P Q charts
    let R := sourceDeletedDualGraph D P marked Q charts
    let gm := phi ((LatticeDrawing.primalGraph D P).left (markedPrimal D P marked)) -
      phi ((LatticeDrawing.primalGraph D P).right (markedPrimal D P marked))
    laplacian R.left R.right eta F =
      (if J.left (markedPrimal D P marked) = F then gm else 0) -
      (if J.right (markedPrimal D P marked) = F then gm else 0) := by
  intro J R gm
  have hl : laplacian R.left R.right eta F =
      -Plane.copyBoundary R.left R.right
        (fun e => phi (copyA D P marked e) - phi (copyB D P marked e)) F := by
    rw [← Plane.copyBoundary_gradient]
    simp only [Plane.copyBoundary, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro e _
    have hs := hstream e
    change eta (R.right e) - eta (R.left e) = _ at hs
    simp only [Plane.copyGradient]
    split_ifs <;> linarith only [hs]
  have hb := hbalance F
  rw [full_boundary_eq_retained_add_marked] at hb
  change Plane.copyBoundary R.left R.right
      (fun e => phi (copyA D P marked e) - phi (copyB D P marked e)) F +
      ((if J.left (markedPrimal D P marked) = F then gm else 0) -
       (if J.right (markedPrimal D P marked) = F then gm else 0)) = 0 at hb
  linarith only [hl, hb]

/-- Reversing either the marked storage orientation or the ordered endpoints reverses
the height sign. The same sign applies to the whole face carrier. -/
theorem marked_residual_sign {W : Type} (a b v0 vm : W) (g : ℝ)
    (hg : g = -1 ∨ g = 1)
    (hends : (a = v0 ∧ b = vm) ∨ (b = v0 ∧ a = vm)) :
    ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧ ∀ F : W,
      ((if a = F then g else 0) - (if b = F then g else 0)) =
        -sigma * ((if F = v0 then (1 : ℝ) else 0) - (if F = vm then 1 else 0)) := by
  classical
  rcases hg with hg | hg
  · rcases hends with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · refine ⟨1, Or.inl rfl, ?_⟩
      intro F
      rw [ha, hb, hg]
      simp only [eq_comm]
      split_ifs <;> norm_num
    · refine ⟨-1, Or.inr rfl, ?_⟩
      intro F
      rw [ha, hb, hg]
      simp only [eq_comm]
      split_ifs <;> norm_num
  · rcases hends with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · refine ⟨-1, Or.inr rfl, ?_⟩
      intro F
      rw [ha, hb, hg]
      simp only [eq_comm]
      split_ifs <;> norm_num
    · refine ⟨1, Or.inl rfl, ?_⟩
      intro F
      rw [ha, hb, hg]
      simp only [eq_comm]
      split_ifs <;> norm_num

/-- The two actual marked storage orientations and either boundary order determine
one global sign. The signed, zero-ground height is the negative original Green row
on every face, not merely on the boundary path. -/
theorem original_height_eq_neg_green
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (LatticeDrawing.primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) [Fintype (Face Q)]
    (v0 vm : Face Q)
    (hc : (supportGraph (sourceDeletedDualGraph D P marked Q charts).left
      (sourceDeletedDualGraph D P marked Q charts).right).Preconnected)
    (hmarked :
      ((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = v0 ∧
        (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vm) ∨
      ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = v0 ∧
        (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vm))
    (eta : Face Q → ℝ)
    (hstream : ∀ e : Copy D P marked,
      eta ((sourceDeletedDualGraph D P marked Q charts).right e) -
        eta ((sourceDeletedDualGraph D P marked Q charts).left e) =
      Repair8.voltage D P hD marked (copyA D P marked e) -
        Repair8.voltage D P hD marked (copyB D P marked e))
    (hbalance : ∀ F : Face Q,
      Plane.copyBoundary (sourceDualGraph D P Q charts).left
        (sourceDualGraph D P Q charts).right
        (Plane.copyGradient (LatticeDrawing.primalGraph D P).left (LatticeDrawing.primalGraph D P).right
          (Repair8.voltage D P hD marked)) F = 0) :
    let R := sourceDeletedDualGraph D P marked Q charts
    ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧
      ∀ F, sigma * (eta F - eta vm) = -groundedGreen R.left R.right vm hc v0 F := by
  intro R
  have hp := Repair8.voltage_spec D P hD marked
  have hl := stream_laplacian_eq_marked_residual D P marked Q charts
    (Repair8.voltage D P hD marked) eta hstream hbalance
  let gm := Repair8.voltage D P hD marked
      ((LatticeDrawing.primalGraph D P).left (markedPrimal D P marked)) -
    Repair8.voltage D P hD marked
      ((LatticeDrawing.primalGraph D P).right (markedPrimal D P marked))
  have hgm : gm = -1 ∨ gm = 1 := by
    rcases marked.property with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · left
      change (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) = alpha D P at ha
      change (LatticeDrawing.primalGraph D P).right (markedPrimal D P marked) = beta D P at hb
      change Repair8.voltage D P hD marked
        ((LatticeDrawing.primalGraph D P).left (markedPrimal D P marked)) -
        Repair8.voltage D P hD marked
        ((LatticeDrawing.primalGraph D P).right (markedPrimal D P marked)) = -1
      rw [ha, hb, hp.1, hp.2.1]
      norm_num
    · right
      change (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) = beta D P at hb
      change (LatticeDrawing.primalGraph D P).right (markedPrimal D P marked) = alpha D P at ha
      change Repair8.voltage D P hD marked
        ((LatticeDrawing.primalGraph D P).left (markedPrimal D P marked)) -
        Repair8.voltage D P hD marked
        ((LatticeDrawing.primalGraph D P).right (markedPrimal D P marked)) = 1
      rw [hb, ha, hp.1, hp.2.1]
      norm_num
  obtain ⟨sigma, hsigma, hsign⟩ := marked_residual_sign
    ((sourceDualGraph D P Q charts).left (markedPrimal D P marked))
    ((sourceDualGraph D P Q charts).right (markedPrimal D P marked)) v0 vm gm hgm hmarked
  have hres (F : Face Q) : laplacian R.left R.right eta F =
      -sigma * ((if F = v0 then (1 : ℝ) else 0) - (if F = vm then 1 else 0)) :=
    (hl F).trans (hsign F)
  have hsq : sigma * sigma = 1 := by
    rcases hsigma with h | h <;> rw [h] <;> norm_num
  have hg : (fun F => -sigma * (eta F - eta vm)) =
      groundedGreen R.left R.right vm hc v0 := by
    apply groundedPoisson_eq R.left R.right vm hc (fun F => if F = v0 then 1 else 0)
    constructor
    · simp only [sub_self, mul_zero]
    · intro F hF
      change laplacian R.left R.right ((-sigma) • (eta - fun _ => eta vm)) F = _
      rw [laplacian_smul, laplacian_sub, laplacian_const, sub_zero, hres F,
        if_neg hF, sub_zero]
      split_ifs <;> nlinarith only [hsq]
  refine ⟨sigma, hsigma, ?_⟩
  intro F
  have hf := congrFun hg F
  change -sigma * (eta F - eta vm) = _ at hf
  linarith only [hf]

end
end FiniteAvalanches.Electrical.Source.CurrentTerminalHeight
