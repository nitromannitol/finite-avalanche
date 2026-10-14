import CurrentS7LovaszApplication

namespace FiniteAvalanches.Electrical.LovaszApplication
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing SplitStep Geometry
open scoped Classical BigOperators
noncomputable section

                                                                          
                                                                              
theorem current_S7_original_family_cutoff (D : Finset (Site 2)) (P : OneSet D)
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
      let G := groundedGreen K.left K.right (W.vertices (Fin.last W.m)) hc (W.vertices 0)
      ∃ R : Copy D P marked → Square,
        (∀ e, (R e).carrier = copiedSquare J phi (fun F => -G F) K.left K.right e) ∧
        (∀ e f, e ≠ f → Disjoint (R e).openCarrier (R f).openCarrier) ∧
        (∀ e, phi (J.left e) = phi (J.right e) →
          (R e).side = 0 ∧ (R e).carrier = {(phi (J.left e), -G (K.left e))}) ∧
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
  obtain ⟨W, _hp0, _hp1, _hM, _hunit, _hclosing, _sigma, _hsigma, _hfield,
    _hdiag, _hground, _hmode, R, hcoords, hd, _hcover, hzero, _hrotation, hcutoff⟩ :=
    current_S7_lovasz_application D P hD hDc hP marked
  exact ⟨W, R, fun e => (hcoords e).2.2.2, hd, hzero, hcutoff⟩

end
end FiniteAvalanches.Electrical.LovaszApplication

#check @FiniteAvalanches.Electrical.LovaszApplication.current_S7_lovasz_application
#check @FiniteAvalanches.Electrical.LovaszApplication.current_S7_original_family_cutoff
#print FiniteAvalanches.Electrical.LovaszApplication.OriginalBoundaryWitness
#print axioms FiniteAvalanches.Electrical.LovaszApplication.current_S7_original_family_cutoff
