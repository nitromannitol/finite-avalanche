import FiniteAvalanches.Electrical.SplitStep.OriginalGraphRecovery20
import FiniteAvalanches.Electrical.Trees.TerminalComplement

/-! Original source graph data for the diagonal identity, on every supplied drawing. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing ChordSplit
open FiniteAvalanches.Wilson.CopiedNetwork
open scoped Classical
noncomputable section
section
attribute [local instance] originalGraphPrecursorCopyDec originalGraphPrecursorVertexDec
  originalGraphPrecursorFaceDec

/-- On every original source drawing, literal complement takes precisely all K trees
to all dual forests separating the stated original path faces. -/
theorem original_tree_twoRootForest_complement_iff21 :
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
      ∀ A : Finset (Copy D P marked),
        ((Set.univ : Set (GroundedSplitVertex (alpha D P) (beta D P))).Nonempty ∧
          (∀ x y, K.reaches A x y) ∧
          ∀ e ∈ A, ¬K.reaches (A.erase e) (K.left e) (K.right e)) ↔
        ((∀ e ∈ Aᶜ, ¬B.reaches (Aᶜ.erase e) (B.left e) (B.right e)) ∧
          ∀ x, ∃ r ∈ ({vertices i, vertices (Fin.last m)} : Set (Face Q)), B.reaches Aᶜ x r ∧
            ∀ r' ∈ ({vertices i, vertices (Fin.last m)} : Set (Face Q)),
              B.reaches Aᶜ x r' → r' = r) := by
  intro D P hD marked Q charts finiteFaces
  letI : Fintype (Face Q) := finiteFaces
  intro m vertices hinj copies hends i hi0 him B K A
  obtain ⟨precursor, ⟨phi, hphi⟩, hu⟩ := original_diagonal_graph_recovery20
    D P hD marked Q charts finiteFaces vertices hinj copies hends i hi0 him
  have hne : vertices i ≠ vertices (Fin.last m) := by
    intro h
    have he := congrArg Fin.val (hinj h)
    simp only [Fin.val_last] at he
    omega
  apply CopiedGraph.terminal_tree_complement_iff K B (Sum.inr false) (Sum.inr true)
    (by intro h; cases h)
    (CopiedGraph.forest_tree_complement_iff_of_equiv K B _ _ phi hphi)
    m vertices (fun k => (copies k).val)
    (fun k l h => copies.injective (Subtype.ext h)) hends i hne
    (original_grounded_star_iff D P marked copies i.val)
    precursor.2.2.2.1 hu A

end

/-- The exact source-universal numerator bijection, with complement as the actual map. -/
theorem original_numerator_complement21 :
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
      ∃ phi : K.SpanningTree ≃ B.TwoRootForest (vertices i) (vertices (Fin.last m)),
        ∀ T : K.SpanningTree, (phi T).val = T.valᶜ
 := by
  intro D P hD marked Q charts finiteFaces
  letI : Fintype (Face Q) := finiteFaces
  intro m vertices hinj copies hends i hi0 him B K
  let hcomp := original_tree_twoRootForest_complement_iff21 D P hD marked Q charts
    finiteFaces vertices hinj copies hends i hi0 him
  refine ⟨CopiedGraph.treeTwoRootForestComplementEquiv K B _ _ hcomp, ?_⟩
  intro T
  rw [CopiedGraph.treeTwoRootForestComplementEquiv_copies]
  ext e
  simp only [Finset.mem_compl]

end
end FiniteAvalanches.Electrical.SplitStep
