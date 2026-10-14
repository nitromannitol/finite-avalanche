import OriginalGreenSquares
import FiniteAvalanches.Electrical.Geometry.SourceDualPath

namespace FiniteAvalanches.Electrical.LovaszApplication
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing LatticeCell SplitStep
open Geometry LovaszStream
open scoped Classical BigOperators
noncomputable section

/-- Geometric source witnesses only. The final application produces this data;
it is not an assumed stream, packing or Green dictionary. -/
structure OriginalBoundaryWitness (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P) where
  q : (ℝ × ℝ) → (ℝ × ℝ)
  continuous_q : Continuous q
  Q : Drawing (LatticeDrawing.primalGraph D P)
  point_eq : ∀ v : D, Q.point (project D P v.val) = q (sitePoint v.val)
  curve_eq : ∀ e t, Q.curve e t = q (unitSegment e.val.1 e.val.2 t.val)
  charts : ∀ e, EdgeChart Q e
  finiteFaces : Fintype (Face Q)
  m : ℕ
  three_le : 3 ≤ m
  vertices : Fin (m + 1) → Face Q
  injective_vertices : Function.Injective vertices
  copies : Fin m ≃ {e : Copy D P marked //
    copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}
  copy_ends : ∀ k : Fin m,
    ((sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.castSucc ∧
      (sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.succ) ∨
    ((sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.castSucc ∧
      (sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.succ)
  marked_ends :
    ((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices 0 ∧
      (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices (Fin.last m)) ∨
    ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices 0 ∧
      (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices (Fin.last m))

/-- Current source drawings, original H-face components and the complete alpha
path are produced by the registered realization and copied bond-cycle inputs. -/
theorem exists_original_boundary_witness (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) : Nonempty (OriginalBoundaryWitness D P marked) := by
  obtain ⟨q, hq, Q, hp, hc, charts, finiteFaces, hdual⟩ :=
    source_deleted_dual_path_of_bond_cycle FiniteAvalanches.External.finite_plane_dual_bond_cycle
      D P hD hDc hP marked
  letI : Fintype (Face Q) := finiteFaces
  obtain ⟨_dualDrawing, _dualCharts, _vertexFaces, _hpoint, _hvertex, _hcross,
    _hparts, _hlocal, _horient, _Hstar, _hsp, _hsc, m, hm, vertices, hinj, copies, hends, hmarked⟩ := hdual
  exact ⟨⟨q, hq, Q, hp, hc, charts, finiteFaces, m, hm, vertices, hinj, copies, hends, hmarked⟩⟩

/-- Every selected boundary copy has the literal source rectangle [0,p] times
[-G(v_j),-G(v_{j+1})], with strictly positive p and its actual voltage current. -/
theorem boundary_green_copy_rectangle (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (W : OriginalBoundaryWitness D P marked) (j : Fin W.m) :
    letI : Fintype (Face W.Q) := W.finiteFaces
    let J := originalGraph D P marked
    let K := sourceDeletedDualGraph D P marked W.Q W.charts
    let hc := source_deleted_dual_preconnected_of_classical D P hD hDc hP marked W.Q W.charts
      FiniteAvalanches.External.finite_plane_dual_connected
      FiniteAvalanches.External.finite_plane_dual_bond_cycle
    let phi := Repair8.voltage D P hD marked
    let G := groundedGreen K.left K.right (W.vertices (Fin.last W.m)) hc (W.vertices 0)
    let p := G (W.vertices j.castSucc) - G (W.vertices j.succ)
    0 < p ∧ p ≤ 1 ∧ |phi (J.left (W.copies j).val) - phi (J.right (W.copies j).val)| = p ∧
      copiedSquare J phi (fun F => -G F) K.left K.right (W.copies j).val =
        Set.Icc 0 p ×ˢ Set.Icc (-G (W.vertices j.castSucc)) (-G (W.vertices j.succ)) := by
  letI : Fintype (Face W.Q) := W.finiteFaces
  dsimp only
  let J := originalGraph D P marked
  let K := sourceDeletedDualGraph D P marked W.Q W.charts
  let hc := source_deleted_dual_preconnected_of_classical D P hD hDc hP marked W.Q W.charts
    FiniteAvalanches.External.finite_plane_dual_connected FiniteAvalanches.External.finite_plane_dual_bond_cycle
  let phi := Repair8.voltage D P hD marked
  let G := groundedGreen K.left K.right (W.vertices (Fin.last W.m)) hc (W.vertices 0)
  let p := G (W.vertices j.castSucc) - G (W.vertices j.succ)
  have hv := original_boundary_voltage_eq_green_drop D P hD hDc hP marked W.Q W.charts
    W.vertices W.injective_vertices W.copies W.copy_ends W.marked_ends j
  change phi (if copyA D P marked (W.copies j).val = alpha D P then
    copyB D P marked (W.copies j).val else copyA D P marked (W.copies j).val) = p at hv
  obtain ⟨hp, hp1⟩ := original_green_drop_pos_le_one D P hD hDc hP marked W.Q W.charts
    W.vertices W.injective_vertices W.copies W.copy_ends W.marked_ends j
  change 0 < p at hp
  change p ≤ 1 at hp1
  have hphi0 : phi (alpha D P) = 0 := (Repair8.voltage_spec D P hD marked).1
  have hinterval : Set.Icc (min (phi (J.left (W.copies j).val)) (phi (J.right (W.copies j).val)))
      (max (phi (J.left (W.copies j).val)) (phi (J.right (W.copies j).val))) = Set.Icc 0 p ∧
      |phi (J.left (W.copies j).val) - phi (J.right (W.copies j).val)| = p := by
    by_cases ha : copyA D P marked (W.copies j).val = alpha D P
    · rw [if_pos ha] at hv
      change Set.Icc (min (phi (copyA D P marked (W.copies j).val))
        (phi (copyB D P marked (W.copies j).val)))
        (max (phi (copyA D P marked (W.copies j).val)) (phi (copyB D P marked (W.copies j).val))) = _ ∧
        |phi (copyA D P marked (W.copies j).val) - phi (copyB D P marked (W.copies j).val)| = p
      rw [ha, hphi0, hv, min_eq_left hp.le, max_eq_right hp.le]
      exact ⟨rfl, by simpa only [zero_sub, abs_neg] using abs_of_nonneg hp.le⟩
    · rw [if_neg ha] at hv
      have hb := (W.copies j).property.resolve_left ha
      change Set.Icc (min (phi (copyA D P marked (W.copies j).val))
        (phi (copyB D P marked (W.copies j).val)))
        (max (phi (copyA D P marked (W.copies j).val)) (phi (copyB D P marked (W.copies j).val))) = _ ∧
        |phi (copyA D P marked (W.copies j).val) - phi (copyB D P marked (W.copies j).val)| = p
      rw [hb, hphi0, hv, min_eq_right hp.le, max_eq_left hp.le]
      exact ⟨rfl, by simpa only [sub_zero] using abs_of_nonneg hp.le⟩
  have horder : -G (W.vertices j.castSucc) ≤ -G (W.vertices j.succ) := by
    change 0 < G (W.vertices j.castSucc) - G (W.vertices j.succ) at hp
    linarith only [hp]
  refine ⟨hp, hp1, hinterval.2, ?_⟩
  change copiedSquare J phi (fun F => -G F) K.left K.right (W.copies j).val = _
  unfold copiedSquare
  rw [hinterval.1]
  rcases W.copy_ends j with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · change K.left (W.copies j).val = W.vertices j.castSucc at hl
    change K.right (W.copies j).val = W.vertices j.succ at hr
    rw [hl, hr, min_eq_left horder, max_eq_right horder]
  · change K.right (W.copies j).val = W.vertices j.castSucc at hl
    change K.left (W.copies j).val = W.vertices j.succ at hr
    rw [hl, hr, min_eq_right horder, max_eq_left horder]

end
end FiniteAvalanches.Electrical.LovaszApplication

#print axioms FiniteAvalanches.Electrical.LovaszApplication.exists_original_boundary_witness
#print axioms FiniteAvalanches.Electrical.LovaszApplication.boundary_green_copy_rectangle
