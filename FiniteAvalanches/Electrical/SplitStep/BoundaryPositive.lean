import FiniteAvalanches.Electrical.SplitStep.OriginalCurrent
import FiniteAvalanches.Electrical.Reference.CellVoltage

set_option autoImplicit false

namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing
open scoped Classical
noncomputable section

/-- The opposite endpoint of every retained alpha copy is the projection of a site in D. -/
theorem boundary_other_endpoint_in_D (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (e : {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) :
    ∃ x : Site 2, x ∈ D ∧
      (if copyA D P marked e.val = alpha D P then copyB D P marked e.val
        else copyA D P marked e.val) = project D P x := by
  have hd := (mem_domainCopies D e.val.val).mp (Finset.mem_filter.mp e.val.property).1
  by_cases ha : copyA D P marked e.val = alpha D P
  · have ho : originalA e.val.val ∉ D := (project_eq_alpha_iff D P _).mp ha
    exact ⟨originalB e.val.val, hd.resolve_left ho, if_pos ha⟩
  · have hb := e.property.resolve_left ha
    have ho : originalB e.val.val ∉ D := (project_eq_alpha_iff D P _).mp hb
    exact ⟨originalA e.val.val, hd.resolve_right ho, if_neg ha⟩

/-- Positivity comes from connectedness inside D and its nonempty held set P. -/
theorem boundary_voltage_pos_le_one (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (e : {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) :
    let p := Repair8.voltage D P hD marked
      (if copyA D P marked e.val = alpha D P then copyB D P marked e.val
        else copyA D P marked e.val)
    0 < p ∧ p ≤ 1 := by
  obtain ⟨x, hx, he⟩ := boundary_other_endpoint_in_D D P marked e
  dsimp only
  rw [he]
  exact ⟨CellVoltage10.voltage_pos_on_D D P hD marked hx,
    (CellVoltage10.voltage_bounds D P hD marked (project D P x)).2⟩

/-- Every original grounded-dual boundary Green drop is strictly positive and at most one. -/
theorem original_green_drop_pos_le_one
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) [Fintype (Face Q)]
    {m : ℕ} (vertices : Fin (m + 1) → Face Q) (hinj : Function.Injective vertices)
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
    (j : Fin m) :
    let J := sourceDeletedDualGraph D P marked Q charts
    let hc := source_deleted_dual_preconnected_of_classical D P hD hDc hP marked Q charts
      FiniteAvalanches.External.finite_plane_dual_connected
      FiniteAvalanches.External.finite_plane_dual_bond_cycle
    let G := groundedGreen J.left J.right (vertices (Fin.last m)) hc
    let p := G (vertices 0) (vertices j.castSucc) - G (vertices 0) (vertices j.succ)
    0 < p ∧ p ≤ 1 := by
  dsimp only
  rw [← original_boundary_voltage_eq_green_drop D P hD hDc hP marked Q charts
    vertices hinj copies hends hmarked j]
  exact boundary_voltage_pos_le_one D P hD marked (copies j)

end
end FiniteAvalanches.Electrical.SplitStep
