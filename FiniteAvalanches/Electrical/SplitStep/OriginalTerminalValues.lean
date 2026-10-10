import FiniteAvalanches.Electrical.SplitStep.SignedTerminalMidpoints
import FiniteAvalanches.Electrical.SplitStep.BoundaryPositive

set_option autoImplicit false

namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing
open scoped Classical
noncomputable section

/-- A single original-star orientation controls both adjacent-j trial values on the original Green carrier. -/
theorem original_terminal_values_of_stream_and_balance (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (LatticeDrawing.primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) [finiteFaces : Fintype (Face Q)] {m : ℕ}
    (vertices : Fin (m + 1) → Face Q) (hinj : Function.Injective vertices)
    (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P})
    (hends : ∀ k : Fin m,
      ((sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.castSucc ∧
        (sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.succ) ∨
      ((sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.castSucc ∧
        (sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.succ))
    (hmarked :
      ((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices 0 ∧
        (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices (Fin.last m)) ∨
      ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices 0 ∧
        (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices (Fin.last m)))
    (hm : 0 < m)
    (hbalance : ∀ F : Face Q,
      Plane.copyBoundary (sourceDualGraph D P Q charts).left
        (sourceDualGraph D P Q charts).right
        (Plane.copyGradient (LatticeDrawing.primalGraph D P).left
          (LatticeDrawing.primalGraph D P).right (fun x => if x = alpha D P then (1 : ℝ) else 0)) F = 0)
    (psi : Face Q → ℝ)
    (hpsi : ∀ e : Copy D P marked,
      psi ((sourceDeletedDualGraph D P marked Q charts).right e) -
        psi ((sourceDeletedDualGraph D P marked Q charts).left e) =
      Repair8.voltage D P hD marked (copyA D P marked e) -
        Repair8.voltage D P hD marked (copyB D P marked e)) :
    let J := sourceDeletedDualGraph D P marked Q charts
    let hc := source_deleted_dual_preconnected_of_classical D P hD hDc hP marked Q charts
      FiniteAvalanches.External.finite_plane_dual_connected
      FiniteAvalanches.External.finite_plane_dual_bond_cycle
    let G := groundedGreen J.left J.right (vertices (Fin.last m)) hc
    let p := fun k : Fin m => G (vertices 0) (vertices k.castSucc) - G (vertices 0) (vertices k.succ)
    let w := fun k : Fin m => (psi (vertices k.castSucc) + psi (vertices k.succ)) / 2
    ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧
      (∀ k, sigma * (psi (vertices k.succ) - psi (vertices k.castSucc)) = p k) ∧
      ∀ (i : Fin (m + 1)) (j : Fin m), (j.val + 1 = i.val ∨ j.val = i.val) →
        0 < p j / 2 ∧ p j / 2 ≤ 1 / 2 ∧
        ∀ k : Fin m, k ≠ j →
          (k.val < i.val → sigma * (w k - w j) ≤ -(p j / 2)) ∧
          (i.val ≤ k.val → p j / 2 ≤ sigma * (w k - w j)) ∧
          signedAngular sigma (p j / 2) (w j) (0, w k) = if k.val < i.val then 0 else 1 := by
  intro J hc G p w
  obtain ⟨sigma, hsigma, hstep⟩ := original_boundary_increments_of_stream_and_balance
    D P hD marked Q charts vertices hinj copies hends hmarked hm hbalance psi hpsi
  have hp (k : Fin m) : 0 < p k ∧ p k ≤ 1 :=
    original_green_drop_pos_le_one D P hD hDc hP marked Q charts vertices hinj copies hends hmarked k
  have hgreen (k : Fin m) : sigma * (psi (vertices k.succ) - psi (vertices k.castSucc)) = p k := by
    exact (hstep k).trans (original_boundary_voltage_eq_green_drop
      D P hD hDc hP marked Q charts vertices hinj copies hends hmarked k)
  refine ⟨sigma, hsigma, hgreen, ?_⟩
  intro i j hj
  have he : 0 < p j / 2 := half_pos (hp j).1
  refine ⟨he, by linarith only [(hp j).2], ?_⟩
  intro k hkj
  have hbounds := signed_terminal_midpoint_bounds (fun r => psi (vertices r)) p
    (fun r => (hp r).1.le) sigma hgreen i j hj k hkj
  refine ⟨hbounds.1, hbounds.2, ?_⟩
  have haxis := signed_angular_axis_values sigma (p j / 2) (w j) (w k) hsigma he
  split_ifs with hki
  · exact haxis.1 (hbounds.1 hki)
  · exact haxis.2 (hbounds.2 (by omega))

end
end FiniteAvalanches.Electrical.SplitStep
