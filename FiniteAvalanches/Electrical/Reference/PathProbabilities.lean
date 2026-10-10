import FiniteAvalanches.Electrical.Geometry.SourceCompatibleDisk
import FiniteAvalanches.Electrical.Reference.ForestDualMoments
import FiniteAvalanches.Electrical.Trees.PathCurrent

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeDrawing
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice
open scoped Classical BigOperators
noncomputable section

/-- On every compatible original path, the Green drops are probabilities under the
full tree law, lie in [0,1], and sum to the original forest mean. -/
theorem source_path_probability_bounds
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) (finiteFaces : Fintype (Face Q)) :
    letI : Fintype (Face Q) := finiteFaces
    ∀ m : ℕ, ∀ vertices : Fin (m + 1) → Face Q,
      Function.Injective vertices →
      ∀ copies : Fin m ≃ {e : Copy D P marked //
        copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P},
      (∀ k : Fin m,
        ((sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.castSucc ∧
          (sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.succ) ∨
        ((sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.castSucc ∧
          (sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.succ)) →
      (((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices 0 ∧
          (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices (Fin.last m)) ∨
        ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices 0 ∧
          (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices (Fin.last m))) →
      let J := sourceDeletedDualGraph D P marked Q charts
      let hc := source_deleted_dual_preconnected_of_classical
        D P hD hDc hP marked Q charts
        FiniteAvalanches.External.finite_plane_dual_connected
        FiniteAvalanches.External.finite_plane_dual_bond_cycle
      let G := groundedGreen J.left J.right (vertices (Fin.last m)) hc
      let p := fun k : Fin m => G (vertices 0) (vertices k.castSucc) -
        G (vertices 0) (vertices k.succ)
      (∀ k, 0 ≤ p k ∧ p k ≤ 1) ∧ (∑ k, p k) = ReferenceMoment.forestMean D P marked := by
  letI : Fintype (Face Q) := finiteFaces
  intro m vertices hinj copies hends hmarked J hc G p
  letI : Fintype J.SpanningTree := Fintype.ofFinite J.SpanningTree
  obtain ⟨drawing, hpoints, hcurves, hcircle⟩ :=
    source_compatible_path_disk D P hD hDc hP marked Q charts finiteFaces
      m vertices hinj (fun i => (copies i).val) (fun i => (copies i).property) hends
  obtain ⟨_hcard, hcount, hlaw⟩ := source_forest_contact_law D P hD marked Q charts
    finiteFaces (Fintype.ofFinite J.SpanningTree) m vertices copies hmarked
  have hcountR : 0 < (Fintype.card J.SpanningTree : ℝ) := Nat.cast_pos.mpr hcount
  have univ_eq (enumeration : Fintype J.SpanningTree) :
      @Finset.univ J.SpanningTree enumeration =
        @Finset.univ J.SpanningTree (Fintype.ofFinite J.SpanningTree) :=
    congrArg (fun f : Fintype J.SpanningTree => @Finset.univ J.SpanningTree f)
      (Subsingleton.elim enumeration _)
  have hcurrent (i : Fin m) :
      (∑ T : J.SpanningTree,
        J.pathIndicator T (vertices 0) (vertices (Fin.last m)) (copies i).val) /
        (Fintype.card J.SpanningTree : ℝ) = p i :=
    by
      have h := drawing.boundary_mean_pathIndicator hc hpoints hcurves m vertices hinj
        (fun i => (copies i).val) hends hcircle i
      simpa only [univ_eq, ← Nat.card_eq_fintype_card] using h
  constructor
  · intro i
    rw [← hcurrent]
    constructor
    · apply div_nonneg _ hcountR.le
      apply Finset.sum_nonneg
      intro T _
      unfold CopiedGraph.pathIndicator
      split_ifs <;> norm_num
    · apply (div_le_one hcountR).mpr
      calc
        _ ≤ ∑ _T : J.SpanningTree, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro T _
          unfold CopiedGraph.pathIndicator
          split_ifs <;> norm_num
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  · have hmean := hlaw id
    change ReferenceMoment.forestMean D P marked =
      (∑ T : J.SpanningTree, ∑ i : Fin m,
        J.pathIndicator T (vertices 0) (vertices (Fin.last m)) (copies i).val) /
        (Fintype.card J.SpanningTree : ℝ) at hmean
    rw [Finset.sum_comm, Finset.sum_div] at hmean
    simp_rw [hcurrent] at hmean
    exact hmean.symm

end
end FiniteAvalanches.Electrical.LatticeDrawing
