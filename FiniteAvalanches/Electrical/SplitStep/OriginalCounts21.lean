import FiniteAvalanches.Electrical.SplitStep.OriginalNumerator21

/-! Original source graph data for the diagonal identity, on every supplied drawing. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing ChordSplit
open FiniteAvalanches.Wilson.CopiedNetwork
open scoped Classical
noncomputable section

/-- Both original copied counts, without a Green or conductance-ratio assumption. -/
theorem original_diagonal_tree_forest_counts21 :
  ∀ (D : Finset (Site 2)) (P : OneSet D)
    (_hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) (finiteFaces : Fintype (Face Q)),
    letI : Fintype (Face Q) := finiteFaces
    ∀ {m : ℕ} (vertices : Fin (m + 1) → Face Q) (_hinj : Function.Injective vertices)
      (copies : Fin m ≃ {e : Copy D P marked //
        copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}),
    (∀ k : Fin m,
      ((sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.castSucc ∧
        (sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.succ) ∨
      ((sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.castSucc ∧
        (sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.succ)) →
    ∀ i : Fin (m + 1), 0 < i.val → i.val < m →
      let B := sourceDeletedDualGraph D P marked Q charts
      let K := groundedSplitGraph (originalGraph D P marked) (alpha D P) (beta D P)
        (boundarySide _ _ _ copies i.val)
      Nat.card K.SpanningTree =
        Nat.card (B.TwoRootForest (vertices i) (vertices (Fin.last m))) ∧
      Nat.card (K.TwoRootForest (Sum.inr false) (Sum.inr true)) = Nat.card B.SpanningTree := by
  intro D P hD marked Q charts finiteFaces
  letI : Fintype (Face Q) := finiteFaces
  intro m vertices hinj copies hends i hi0 him B K
  obtain ⟨phi, _hphi⟩ := original_numerator_complement21 D P hD marked Q charts
    finiteFaces vertices hinj copies hends i hi0 him
  obtain ⟨_precursor, ⟨psi, _hpsi⟩, _hu⟩ := original_diagonal_graph_recovery20
    D P hD marked Q charts finiteFaces vertices hinj copies hends i hi0 him
  exact ⟨Nat.card_congr phi, Nat.card_congr psi⟩

end
end FiniteAvalanches.Electrical.SplitStep
