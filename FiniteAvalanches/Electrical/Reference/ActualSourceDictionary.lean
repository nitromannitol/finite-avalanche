import FiniteAvalanches.Electrical.Reference.ActualSourceForestDualConsumer
import FiniteAvalanches.External.PlaneTreeComplement

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeDrawing
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeCell
open scoped Classical BigOperators
noncomputable section

/-- Original-copy forest and dual-tree contact identities with one shared source drawing. -/
theorem actual_source_forest_dual_dictionary
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) :
    ∃ q : Plane → Plane, Continuous q ∧ ∃ Q : Drawing (primalGraph D P),
      (∀ v : D, Q.point (project D P v.val) = q (sitePoint v.val)) ∧
      (∀ e t, Q.curve e t = q (unitSegment e.val.1 e.val.2 t.val)) ∧
    ∃ charts : ∀ e, EdgeChart Q e,
    ∃ finiteFaces : Fintype (Face Q),
      letI : Fintype (Face Q) := finiteFaces
      let J := sourceDeletedDualGraph D P marked Q charts
      letI : Fintype J.SpanningTree := Fintype.ofFinite J.SpanningTree
      ∃ m : ℕ, 3 ≤ m ∧ ∃ vertices : Fin (m + 1) → Face Q,
        Function.Injective vertices ∧ ∃ copies : Fin m → Copy D P marked,
          Function.Injective (fun i => (copies i).val) ∧
          (∀ e : Copy D P marked, (∃ i, copies i = e) ↔
            copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P) ∧
          (∀ i : Fin m,
            (J.left (copies i) = vertices i.castSucc ∧
              J.right (copies i) = vertices i.succ) ∨
            (J.right (copies i) = vertices i.castSucc ∧
              J.left (copies i) = vertices i.succ)) ∧
          (∀ i : Fin m, (copies i).val ≠ marked.val) ∧
          (((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices 0 ∧
              (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices (Fin.last m)) ∨
            ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices 0 ∧
              (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices (Fin.last m))) ∧
          (∃ hconn : (supportGraph J.left
            J.right).Preconnected,
          (∀ F G : Face Q,
            J.reaches Finset.univ F G) ∧
        ∃ Hstar : Drawing J,
        ∃ outerFace : Face Hstar,
          ¬Bornology.IsBounded (faceRegion Hstar outerFace) ∧
          (Set.range (fun k => Hstar.point (vertices k)) ∪
            ⋃ i : Fin m, Set.range (Hstar.curve (copies i))) ⊆
              frontier (faceRegion Hstar outerFace) ∧
        ∃ diskDrawing : Drawing J,
          (∀ F : Face Q, diskDrawing.point F ∈ disk) ∧
          (∀ e t, diskDrawing.curve e t ∈ disk) ∧
          (∀ i t, diskDrawing.curve (copies i) t ∈ circle) ∧
          (∀ e : Copy D P marked,
            copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P →
              Set.range (diskDrawing.curve e) ⊆ circle) ∧
        ∃ θ : Fin (m + 1) → ℝ,
          StrictMono θ ∧
          θ (Fin.last m) < θ 0 + 2 * Real.pi ∧
          (∀ k, diskDrawing.point (vertices k) = (Real.cos (θ k), Real.sin (θ k))) ∧
          0 < Fintype.card J.SpanningTree ∧
          (Fintype.card J.SpanningTree : ℝ) ≠ 0 ∧
          ∃ forestDual : ReferenceMoment.Forest D P marked ≃ J.SpanningTree,
            (∀ F, (forestDual F).val = F.valᶜ) ∧
            Fintype.card (ReferenceMoment.Forest D P marked) = Fintype.card J.SpanningTree ∧
            (∀ (F : ReferenceMoment.Forest D P marked) (i : Fin m),
              (if (StatementTypes.graph D P marked).reaches F.val (if copyA D P marked (copies i) = alpha D P then copyB D P marked (copies i) else copyA D P marked (copies i)) (beta D P) then (1 : ℝ) else 0) =
                J.pathIndicator (forestDual F) (vertices 0) (vertices (Fin.last m)) (copies i)) ∧
            (∀ F : ReferenceMoment.Forest D P marked,
              ReferenceMoment.boundaryContacts D P marked F =
                ∑ i : Fin m, J.pathIndicator (forestDual F) (vertices 0)
                  (vertices (Fin.last m)) (copies i)) ∧
            ReferenceMoment.forestMean D P marked =
              (∑ T : J.SpanningTree, ∑ i : Fin m,
                J.pathIndicator T (vertices 0) (vertices (Fin.last m)) (copies i)) /
                (Fintype.card J.SpanningTree : ℝ) ∧
            (∀ (indices : Finset (Fin m)),
              (∑ F : ReferenceMoment.Forest D P marked, ∏ i ∈ indices,
                (if (StatementTypes.graph D P marked).reaches F.val (if copyA D P marked (copies i) = alpha D P then copyB D P marked (copies i) else copyA D P marked (copies i)) (beta D P) then (1 : ℝ) else 0)) / (Fintype.card (ReferenceMoment.Forest D P marked) : ℝ) =
              (∑ T : J.SpanningTree, ∏ i ∈ indices,
                J.pathIndicator T (vertices 0) (vertices (Fin.last m)) (copies i)) /
                (Fintype.card J.SpanningTree : ℝ)) ∧
            (∀ (i j : Fin m),
              (∑ F : ReferenceMoment.Forest D P marked,
                (if (StatementTypes.graph D P marked).reaches F.val (if copyA D P marked (copies i) = alpha D P then copyB D P marked (copies i) else copyA D P marked (copies i)) (beta D P) then (1 : ℝ) else 0) *
                (if (StatementTypes.graph D P marked).reaches F.val (if copyA D P marked (copies j) = alpha D P then copyB D P marked (copies j) else copyA D P marked (copies j)) (beta D P) then (1 : ℝ) else 0)) /
                  (Fintype.card (ReferenceMoment.Forest D P marked) : ℝ) =
              (∑ T : J.SpanningTree,
                J.pathIndicator T (vertices 0) (vertices (Fin.last m)) (copies i) *
                J.pathIndicator T (vertices 0) (vertices (Fin.last m)) (copies j)) /
                  (Fintype.card J.SpanningTree : ℝ)) ∧
          ∀ (i j : Fin m), i.val < j.val →
            let G := groundedGreen J.left J.right (vertices (Fin.last m)) hconn
            (∑ T : J.SpanningTree,
              J.pathIndicator T (vertices 0) (vertices (Fin.last m)) (copies i) *
              J.pathIndicator T (vertices 0) (vertices (Fin.last m)) (copies j)) /
                (Fintype.card J.SpanningTree : ℝ) =
              G (vertices 0) (vertices i.castSucc) *
                (G (vertices i.succ) (vertices j.castSucc) - G (vertices i.succ) (vertices j.succ)) -
              G (vertices 0) (vertices i.succ) *
                (G (vertices i.castSucc) (vertices j.castSucc) - G (vertices i.castSucc) (vertices j.succ)) -
              G (vertices 0) (vertices j.castSucc) *
                (G (vertices i.castSucc) (vertices j.succ) - G (vertices i.succ) (vertices j.succ)) +
              G (vertices 0) (vertices j.succ) *
                (G (vertices i.castSucc) (vertices j.castSucc) - G (vertices i.succ) (vertices j.castSucc))) := by
  exact actual_source_forest_dual_dictionary_of_tree_complement FiniteAvalanches.External.finite_plane_tree_complement D P hD hDc hP marked

end
end FiniteAvalanches.Electrical.LatticeDrawing
