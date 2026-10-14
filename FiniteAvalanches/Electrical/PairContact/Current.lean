import FiniteAvalanches.Electrical.PairContact.ActualSourceTreeTwoContact

/-! Pair contacts on the original marked-copy-deleted network. -/
namespace FiniteAvalanches.Electrical.Source
open LatticeProb
open FiniteAvalanches.Electrical
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.LatticeDrawing
open FiniteAvalanches.Electrical.BSST
open FiniteAvalanches.Electrical.Plane.SourceLattice
open FiniteAvalanches.Electrical.LatticeCell
open scoped Classical BigOperators
noncomputable section

/-- The actual source deleted-dual tree two-contact identity, with one shared geometry for all pairs. -/
theorem pair_contact_current
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
  exact LatticeDrawing.actual_source_deleted_dual_tree_two_contact D P hD hDc hP marked

end
end FiniteAvalanches.Electrical.Source
