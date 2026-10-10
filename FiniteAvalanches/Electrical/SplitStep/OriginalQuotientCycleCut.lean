import FiniteAvalanches.Electrical.SplitStep.OriginalAllEdgeComplement
import FiniteAvalanches.Electrical.Trees.SeparatingForestCompletionIff

/-! The removable-cycle dictionary on the all-edge quotient itself. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing ChordSplit
open FiniteAvalanches.Wilson.CopiedNetwork
open scoped Classical
noncomputable section

local instance originalQuotientCycleCutCopyDec (D : Finset (Site 2))
    (P : OneSet D) (marked : MarkedCopy D P) : DecidableEq (Copy D P marked) :=
  Classical.decEq _

/-- Removability of every original ID is exactly crossing of the two dual forest components. -/
theorem original_quotient_erase_tree_iff
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) (finiteFaces : Fintype (Face Q)) :
    letI : Fintype (Face Q) := finiteFaces
    ∀ (u v : Face Q), u ≠ v →
    ∀ F : (sourceDeletedDualGraph D P marked Q charts).TwoRootForest u v,
    ∀ e : Copy D P marked,
      ((Set.univ : Set (NonemptyQuotient.Vertex (pairRoots (alpha D P) (beta D P)))).Nonempty ∧
        (∀ x y, (originalAllEdgeQuotient D P marked).reaches (F.valᶜ.erase e) x y) ∧
        ∀ f ∈ F.valᶜ.erase e,
          ¬(originalAllEdgeQuotient D P marked).reaches ((F.valᶜ.erase e).erase f)
            ((originalAllEdgeQuotient D P marked).left f)
            ((originalAllEdgeQuotient D P marked).right f)) ↔
      ¬(sourceDeletedDualGraph D P marked Q charts).reaches F.val
        ((sourceDeletedDualGraph D P marked Q charts).left e)
        ((sourceDeletedDualGraph D P marked Q charts).right e) := by
  letI : Fintype (Face Q) := finiteFaces
  intro u v hne F e
  have h := original_allEdge_tree_complement_iff D P hD marked Q charts finiteFaces
    (F.valᶜ.erase e)
  rw [Finset.compl_erase, compl_compl] at h
  exact h.trans (CopiedGraph.twoRootForest_insert_tree_iff _ u v hne F e)

/-- A separating forest complement is a quotient tree plus a retained suffix ID. -/
theorem original_quotient_tree_plus_suffix
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) (finiteFaces : Fintype (Face Q)) :
    letI : Fintype (Face Q) := finiteFaces
    ∀ {m : ℕ} (vertices : Fin (m + 1) → Face Q) (_hinj : Function.Injective vertices)
      (copies : Fin m ≃ {e : Copy D P marked //
        copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}),
    (∀ k : Fin m,
      ((sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.castSucc ∧
        (sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.succ) ∨
      ((sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.castSucc ∧
        (sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.succ)) →
    ∀ i : Fin (m + 1), i.val < m →
    ∀ F : (sourceDeletedDualGraph D P marked Q charts).TwoRootForest
      (vertices i) (vertices (Fin.last m)),
    ∃ k : Fin m, i.val ≤ k.val ∧ (copies k).val ∉ F.val ∧
      ∃ T : (originalAllEdgeQuotient D P marked).SpanningTree,
        T.val = F.valᶜ.erase (copies k).val ∧
          insert (copies k).val T.val = F.valᶜ := by
  letI : Fintype (Face Q) := finiteFaces
  intro m vertices hinj copies hends i him F
  let B := sourceDeletedDualGraph D P marked Q charts
  have hne : vertices i ≠ vertices (Fin.last m) := by
    intro h
    have hi := congrArg Fin.val (hinj h)
    simp only [Fin.val_last] at hi
    omega
  obtain ⟨k, hik, hsep⟩ := CopiedGraph.exists_suffix_crossing_copy B m vertices
    (fun k => (copies k).val) hends i F.val
    (CopiedGraph.twoRootForest_roots_separated B _ _ hne F)
  have he : (copies k).val ∉ F.val := fun he =>
    hsep (.single ⟨(copies k).val, he, Or.inl ⟨rfl, rfl⟩⟩)
  have ht := (original_quotient_erase_tree_iff D P hD marked Q charts finiteFaces
    _ _ hne F (copies k).val).mpr hsep
  exact ⟨k, hik, he, ⟨_, ht⟩, rfl, Finset.insert_erase (Finset.mem_compl.mpr he)⟩

end
end FiniteAvalanches.Electrical.SplitStep
