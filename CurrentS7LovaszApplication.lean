import CurrentOriginalBoundary

namespace FiniteAvalanches.Electrical.LovaszApplication
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing SplitStep
open Geometry LovaszStream
open scoped Classical BigOperators
noncomputable section

/-- Closed application of the selected Lovasz construction to the current S7
original-copy family. All drawing, chart, face, path, stream, Green, packing,
coverage and positive boundary cutoff obligations are produced inside the proof. -/
theorem current_S7_lovasz_application (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) :
    ∃ W : OriginalBoundaryWitness D P marked,
      letI : Fintype (Face W.Q) := W.finiteFaces
      let J := originalGraph D P marked
      let K := sourceDeletedDualGraph D P marked W.Q W.charts
      let hc := source_deleted_dual_preconnected_of_classical D P hD hDc hP marked W.Q W.charts
        FiniteAvalanches.External.finite_plane_dual_connected
        FiniteAvalanches.External.finite_plane_dual_bond_cycle
      let phi := Repair8.voltage D P hD marked
      let eta := originalStream D P hD marked W.Q W.charts
      let v0 := W.vertices 0
      let vm := W.vertices (Fin.last W.m)
      let G := groundedGreen K.left K.right vm hc v0
      let M := mass J phi
      phi (alpha D P) = 0 ∧ phi (beta D P) = 1 ∧ 0 < M ∧
      (∀ F : Face W.Q, laplacian K.left K.right G F =
        (if F = v0 then 1 else 0) - (if F = vm then 1 else 0)) ∧
      (∀ x : Vertex D P, Plane.copyBoundary (augmentedGraph J (alpha D P) (beta D P)).left
        (augmentedGraph J (alpha D P) (beta D P)).right
        (Plane.physicalArcFlow J.left J.right phi M) x = 0) ∧
      ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧
        (∀ F : Face W.Q, sigma * (eta F - eta vm) = -G F) ∧ G v0 = M ∧ G vm = 0 ∧
        ((sigma = 1 ∧ eta v0 = 0 ∧ eta vm = M) ∨
          (sigma = -1 ∧ eta v0 = M ∧ eta vm = 0)) ∧
      ∃ R : Copy D P marked → Square,
        (∀ e, (R e).x = min (phi (J.left e)) (phi (J.right e)) ∧
          (R e).y = min (-G (K.left e)) (-G (K.right e)) ∧
          (R e).side = |phi (J.left e) - phi (J.right e)| ∧
          (R e).carrier = copiedSquare J phi (fun F => -G F) K.left K.right e) ∧
        (∀ e f, e ≠ f → Disjoint (R e).openCarrier (R f).openCarrier) ∧
        (⋃ e, (R e).carrier) = Set.Icc 0 1 ×ˢ Set.Icc (-M) 0 ∧
        (∀ e, phi (J.left e) = phi (J.right e) →
          (R e).side = 0 ∧ (R e).carrier = {(phi (J.left e), -G (K.left e))}) ∧
        (∀ e, (R e).carrier = GeometryReview.quarterTurn ''
          LovaszCoordinates.voltageVerticalSquare J phi G K.left K.right e) ∧
        (∀ j : Fin W.m,
          let p := G (W.vertices j.castSucc) - G (W.vertices j.succ)
          ∃ hp : 0 < p, p ≤ 1 ∧ (R (W.copies j).val).side = p ∧
            (R (W.copies j).val).carrier =
              Set.Icc 0 p ×ˢ Set.Icc (-G (W.vertices j.castSucc)) (-G (W.vertices j.succ)) ∧
            (∑ e : Copy D P marked,
              ((R e).angularOsc (p / 2)
                (-(G (W.vertices j.castSucc) + G (W.vertices j.succ)) / 2)
                1 (by norm_num) (by linarith only [hp]))^2) ≤
                16 * (1 + Real.log (2 / p))) := by
  obtain ⟨W⟩ := exists_original_boundary_witness D P hD hDc hP marked
  refine ⟨W, ?_⟩
  letI : Fintype (Face W.Q) := W.finiteFaces
  dsimp only
  let J := originalGraph D P marked
  let K := sourceDeletedDualGraph D P marked W.Q W.charts
  let hc := source_deleted_dual_preconnected_of_classical D P hD hDc hP marked W.Q W.charts
    FiniteAvalanches.External.finite_plane_dual_connected FiniteAvalanches.External.finite_plane_dual_bond_cycle
  let phi := Repair8.voltage D P hD marked
  let eta := originalStream D P hD marked W.Q W.charts
  let v0 := W.vertices 0
  let vm := W.vertices (Fin.last W.m)
  let G := groundedGreen K.left K.right vm hc v0
  let M := mass J phi
  have hne : v0 ≠ vm := by
    intro h
    have hi := congrArg Fin.val (W.injective_vertices h)
    change 0 = W.m at hi
    have hm := W.three_le
    omega
  have hends : alpha D P ≠ beta D P := by intro h; cases h
  have hp := Repair8.voltage_spec D P hD marked
  have hM := Lovasz.mass_pos_of_normalized_boundary J (alpha D P) (beta D P)
    (Repair8.graph_connected D P hD marked).preconnected phi hp.1 hp.2.1
  obtain ⟨sigma, hsigma, hfield, hdiag, hground, hmode⟩ :=
    constructed_original_green_normalization D P hD marked W.Q W.charts v0 vm hc W.marked_ends
  obtain ⟨R, hcoords, hd, hcover, hzero, hsum⟩ :=
    constructed_original_square_family D P hD marked W.Q W.charts v0 vm hc W.marked_ends
  obtain ⟨_hlength, _hdisj, _hclosed, _hpoint, hquarterTurn⟩ :=
    constructed_original_green_tiling D P hD marked W.Q W.charts v0 vm hc W.marked_ends
  refine ⟨hp.1, hp.2.1, hM,
    original_green_unit_laplacian D P marked W.Q W.charts v0 vm hc hne,
    physical_current_balanced J (alpha D P) (beta D P) hends phi hp.1 hp.2.1 hp.2.2,
    sigma, hsigma, hfield, hdiag, hground, hmode, R, hcoords, hd, hcover, hzero, ?_, ?_⟩
  · intro e
    exact (hcoords e).2.2.2 |>.trans (hquarterTurn e)
  · intro j
    let p := G (W.vertices j.castSucc) - G (W.vertices j.succ)
    obtain ⟨hpos, hp1, hside, hrectangle⟩ :=
      boundary_green_copy_rectangle D P hD hDc hP marked W j
    change 0 < p at hpos
    change p ≤ 1 at hp1
    refine ⟨hpos, hp1, (hcoords (W.copies j).val).2.2.1 |>.trans hside,
      (hcoords (W.copies j).val).2.2.2 |>.trans hrectangle, ?_⟩
    have he : 0 < p / 2 := by linarith only [hpos]
    have he1 : p / 2 ≤ 1 := by linarith only [hp1]
    have hr : 1 / (p / 2) = 2 / p := by ring
    have hb := hsum (p / 2) (-(G (W.vertices j.castSucc) + G (W.vertices j.succ)) / 2) he he1
    simpa only [hr] using hb

end
end FiniteAvalanches.Electrical.LovaszApplication

#print axioms FiniteAvalanches.Electrical.LovaszApplication.current_S7_lovasz_application
