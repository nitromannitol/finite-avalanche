import FiniteAvalanches.Electrical.Reference.ConjugateMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Electrical.Plane.SourceLattice.ReferenceMoment
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing SplitStep
open LatticeCell
open scoped Classical BigOperators
noncomputable section

/-- The final source means lemma on a constructed drawing of the original H.
Every identity uses this same full face carrier and boundary enumeration. -/
theorem boundary_means
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) :
  ∃ q : Plane → Plane, Continuous q ∧
    ∃ Q : Drawing (FiniteAvalanches.Electrical.LatticeDrawing.primalGraph D P),
      (∀ v : D, Q.point (project D P v.val) = q (sitePoint v.val)) ∧
      (∀ e t, Q.curve e t = q (unitSegment e.val.1 e.val.2 t.val)) ∧
      ∃ charts : ∀ e, EdgeChart Q e,
      ∃ finiteFaces : Fintype (Face Q),
      letI : Fintype (Face Q) := finiteFaces
      ∃ m : ℕ, ∃ vertices : Fin (m + 1) → Face Q,
        Function.Injective vertices ∧
        ∃ copies : Fin m ≃ {e : Copy D P marked //
          copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P},
          (∀ k : Fin m,
            ((sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.castSucc ∧
              (sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.succ) ∨
            ((sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.castSucc ∧
              (sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.succ)) ∧
          (((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices 0 ∧
              (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices (Fin.last m)) ∨
            ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices 0 ∧
              (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices (Fin.last m))) ∧
    let J := sourceDeletedDualGraph D P marked Q charts
    let hc := source_deleted_dual_preconnected_of_classical D P hD hDc hP marked Q charts
      FiniteAvalanches.External.finite_plane_dual_connected
      FiniteAvalanches.External.finite_plane_dual_bond_cycle
    let G := groundedGreen J.left J.right (vertices (Fin.last m)) hc
    let phi := Repair8.voltage D P hD marked
    let F := ReferenceMoment.Forest D P marked
    letI : Fintype J.SpanningTree := Fintype.ofFinite J.SpanningTree
    (∀ e : Copy D P marked,
      |G (vertices 0) (J.left e) - G (vertices 0) (J.right e)| =
        |phi (copyA D P marked e) - phi (copyB D P marked e)|) ∧
    (∀ i : Fin m,
      let x := if copyA D P marked (copies i).val = alpha D P
        then copyB D P marked (copies i).val else copyA D P marked (copies i).val
      let I : F → ℝ := fun f =>
        if (StatementTypes.graph D P marked).reaches f.val x (beta D P) then 1 else 0
      G (vertices 0) (vertices i.castSucc) - G (vertices 0) (vertices i.succ) = phi x ∧
      phi x = (∑ f : F, I f) / (Fintype.card F : ℝ) ∧
      (∑ f : F, I f) / (Fintype.card F : ℝ) =
        (∑ T : J.SpanningTree,
          J.pathIndicator T (vertices 0) (vertices (Fin.last m)) (copies i).val) /
          (Fintype.card J.SpanningTree : ℝ)) ∧
    ReferenceMoment.forestMean D P marked = G (vertices 0) (vertices 0) ∧
    G (vertices 0) (vertices 0) = energy (copyA D P marked) (copyB D P marked) phi := by
  obtain ⟨q, hq, Q, hpoints, hcurves, charts, finiteFaces,
    m, vertices, hinj, copies, hends, hmarked⟩ :=
      original_split_geometry22 D P hD hDc hP marked
  letI : Fintype (Face Q) := finiteFaces
  exact ⟨q, hq, Q, hpoints, hcurves, charts, finiteFaces,
    m, vertices, hinj, copies, hends, hmarked,
    boundary_means_on_source_drawing D P hD hDc hP marked Q charts vertices hinj copies hends hmarked⟩

end
end FiniteAvalanches.Electrical.Plane.SourceLattice.ReferenceMoment

#print FiniteAvalanches.Electrical.Plane.SourceLattice.ReferenceMoment.boundary_means
#print axioms FiniteAvalanches.Electrical.Plane.SourceLattice.ReferenceMoment.boundary_means
