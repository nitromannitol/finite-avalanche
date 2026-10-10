import FiniteAvalanches.Electrical.SplitStep.OriginalQuotientCycleCut
import FiniteAvalanches.Electrical.SplitStep.OriginalSuffixStar
import FiniteAvalanches.Electrical.Trees.UnicycleIncidentBound
import FiniteAvalanches.Electrical.Trees.SuffixCutParity
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! The complete cut of an original separating dual forest crosses the actual suffix exactly once. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing ChordSplit
open FiniteAvalanches.Wilson.CopiedNetwork
open scoped Classical BigOperators
noncomputable section

local instance originalUniqueSuffixCopyDec (D : Finset (Site 2))
    (P : OneSet D) (marked : MarkedCopy D P) : DecidableEq (Copy D P marked) :=
  Classical.decEq _

/-- Every separating forest on all original dual faces has one and only one suffix cut copy. -/
theorem original_twoRootForest_unique_suffix_cut
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
    ∃! k : Fin m, i.val ≤ k.val ∧
      ¬(sourceDeletedDualGraph D P marked Q charts).reaches F.val
        ((sourceDeletedDualGraph D P marked Q charts).left (copies k).val)
        ((sourceDeletedDualGraph D P marked Q charts).right (copies k).val) := by
  letI : Fintype (Face Q) := finiteFaces
  intro m vertices hinj copies hends i him F
  let B := sourceDeletedDualGraph D P marked Q charts
  let Y := originalAllEdgeQuotient D P marked
  let S : Finset (Fin m) := Finset.univ.filter (fun k => i.val ≤ k.val ∧
    ¬B.reaches F.val (B.left (copies k).val) (B.right (copies k).val))
  have hne : vertices i ≠ vertices (Fin.last m) := by
    intro h
    have hi := congrArg Fin.val (hinj h)
    simp only [Fin.val_last] at hi
    omega
  have copyinj : Function.Injective (fun k : Fin m => (copies k).val) := by
    intro k l h
    exact copies.injective (Subtype.ext h)
  have hidentified := original_identify_grounded_graph D P marked copies i.val
  have atRoot (k : Fin m) (hik : i.val ≤ k.val) :
      Y.left (copies k).val = none ∨ Y.right (copies k).val = none := by
    have hstar := (original_grounded_star_iff D P marked copies i.val (copies k).val).mpr
      ⟨k, hik, rfl⟩
    have hl := congrArg (fun J => J.left (copies k).val) hidentified
    have hr := congrArg (fun J => J.right (copies k).val) hidentified
    rcases hstar with hlK | hrK
    · exact Or.inl (hl.symm.trans
        (congrArg (identifyGroundedTerminals (alpha D P) (beta D P)) hlK))
    · exact Or.inr (hr.symm.trans
        (congrArg (identifyGroundedTerminals (alpha D P) (beta D P)) hrK))
  obtain ⟨k, hik, hkF, T, hT, hU⟩ := original_quotient_tree_plus_suffix
    D P hD marked Q charts finiteFaces vertices hinj copies hends i him F
  have hc : (copies k).val ∉ T.val := by
    rw [hT]
    exact Finset.notMem_erase _ _
  have hbound : (S.image (fun k => (copies k).val)).card ≤ 2 := by
    apply CopiedGraph.unicycle_incident_card_le_two Y T none (copies k).val hc (atRoot k hik)
    intro e he
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp he
    have hl' := (Finset.mem_filter.mp hl).2
    have heF : (copies l).val ∉ F.val := fun heF =>
      hl'.2 (.single ⟨(copies l).val, heF, Or.inl ⟨rfl, rfl⟩⟩)
    have htree := (original_quotient_erase_tree_iff D P hD marked Q charts finiteFaces
      _ _ hne F (copies l).val).mpr hl'.2
    refine ⟨?_, atRoot l hl'.1, ?_⟩
    · rw [hU]
      exact Finset.mem_compl.mpr heF
    · rw [hU]
      exact htree
  rw [Finset.card_image_of_injective S copyinj] at hbound
  have hparity : (S.card : ZMod 2) = 1 := by
    have h := CopiedGraph.twoRootForest_suffix_cut_parity B m vertices
      (fun k => (copies k).val) hends i hne F
    rw [Finset.sum_boole] at h
    exact h
  have hcard : S.card = 1 := by
    by_cases hzero : S.card = 0
    · norm_num [hzero] at hparity
    · by_cases hone : S.card = 1
      · exact hone
      · have htwo : S.card = 2 := by omega
        rw [htwo] at hparity
        have htwoZ : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
        exact (zero_ne_one (htwoZ.symm.trans hparity)).elim
  obtain ⟨l, hl, hu⟩ := Finset.card_eq_one_iff_existsUnique.mp hcard
  exact ⟨l, (Finset.mem_filter.mp hl).2,
    fun j hj => hu j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)⟩

end
end FiniteAvalanches.Electrical.SplitStep
