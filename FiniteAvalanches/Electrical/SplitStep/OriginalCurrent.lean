import FiniteAvalanches.Electrical.SplitStep.OriginalBoundaryDrawing
import FiniteAvalanches.Electrical.SplitStep.ActualEnergy
import FiniteAvalanches.Electrical.Reference.ForestDualDictionary
import FiniteAvalanches.Electrical.Reference.FirstMoment
import FiniteAvalanches.Electrical.Trees.BoundaryTraversal
import FiniteAvalanches.Electrical.Green.FiniteTelescoping
import FiniteAvalanches.External.PlaneTreeComplement
import FiniteAvalanches.External.KirchhoffTreePathCurrent

set_option autoImplicit false

namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing
open scoped Classical BigOperators
noncomputable section

/-- The registered signed-current theorem specializes to an unsigned boundary Green drop. -/
theorem boundary_indicator_mean_eq_green_drop {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (B : Drawing J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (m : ℕ) (vertices : Fin (m + 1) → V) (hinj : Function.Injective vertices)
    (copies : Fin m → E)
    (hends : ∀ k, (J.left (copies k) = vertices k.castSucc ∧ J.right (copies k) = vertices k.succ) ∨
      (J.right (copies k) = vertices k.castSucc ∧ J.left (copies k) = vertices k.succ))
    (hpoints : ∀ x, B.point x ∈ disk) (hcurves : ∀ e t, B.curve e t ∈ disk)
    (hcircle : ∀ k t, B.curve (copies k) t ∈ circle) (k : Fin m) :
    letI : Fintype J.SpanningTree := Fintype.ofFinite J.SpanningTree
    (∑ T : J.SpanningTree, J.pathIndicator T (vertices 0) (vertices (Fin.last m)) (copies k)) /
      (Fintype.card J.SpanningTree : ℝ) =
    groundedGreen J.left J.right (vertices (Fin.last m)) hc (vertices 0) (vertices k.castSucc) -
      groundedGreen J.left J.right (vertices (Fin.last m)) hc (vertices 0) (vertices k.succ) := by
  have hne : vertices 0 ≠ vertices (Fin.last m) := by
    intro h
    have hv := congrArg Fin.val (hinj h)
    have := k.isLt
    simp only [Fin.val_zero, Fin.val_last] at hv
    omega
  have h := (B.boundary_first_moment_iff hpoints hcurves m vertices hinj copies hends hcircle hc k).mpr
    (FiniteAvalanches.External.kirchhoff_meanTreePathCurrent J (vertices (Fin.last m)) hc
      (vertices 0) hne (copies k))
  have univ_eq : ∀ enumeration : Fintype J.SpanningTree,
      @Finset.univ J.SpanningTree enumeration =
        @Finset.univ J.SpanningTree (Fintype.ofFinite J.SpanningTree) := fun enumeration =>
    congrArg (fun f : Fintype J.SpanningTree => @Finset.univ J.SpanningTree f)
      (Subsingleton.elim enumeration _)
  have card_eq : ∀ enumeration : Fintype J.SpanningTree,
      @Fintype.card J.SpanningTree enumeration =
        @Fintype.card J.SpanningTree (Fintype.ofFinite J.SpanningTree) := fun enumeration =>
    congrArg (fun f : Fintype J.SpanningTree => @Fintype.card J.SpanningTree f)
      (Subsingleton.elim enumeration _)
  simpa only [univ_eq, card_eq] using h

variable (D : Finset (Site 2)) (P : OneSet D)
  (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
  (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
  (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
  (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
  (charts : ∀ e, EdgeChart Q e) [finiteFaces : Fintype (Face Q)]
  {m : ℕ} (vertices : Fin (m + 1) → Face Q) (hinj : Function.Injective vertices)
  (copies : Fin m ≃ {e : Copy D P marked //
    copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P})
  (hends : ∀ k : Fin m,
    ((sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.castSucc ∧
      (sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.succ) ∨
    ((sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.castSucc ∧
      (sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.succ))
  (hmarked :
    ((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices 0 ∧
      (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices (Fin.last m)) ∨
    ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices 0 ∧
      (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices (Fin.last m)))

include hD hmarked

/-- Whole-carrier uniform forest means transport through the registered original-Q bijection. -/
theorem original_boundary_color_average_eq_tree_average (k : Fin m) :
    let J := sourceDeletedDualGraph D P marked Q charts
    letI : Fintype J.SpanningTree := Fintype.ofFinite J.SpanningTree
    let x := if copyA D P marked (copies k).val = alpha D P
      then copyB D P marked (copies k).val else copyA D P marked (copies k).val
    (∑ F : ReferenceMoment.Forest D P marked,
      if (StatementTypes.graph D P marked).reaches F.val x (beta D P) then (1 : ℝ) else 0) /
      (Fintype.card (ReferenceMoment.Forest D P marked) : ℝ) =
    (∑ T : J.SpanningTree,
      J.pathIndicator T (vertices 0) (vertices (Fin.last m)) (copies k).val) /
      (Fintype.card J.SpanningTree : ℝ) := by
  let J := sourceDeletedDualGraph D P marked Q charts
  letI : Fintype J.SpanningTree := Fintype.ofFinite J.SpanningTree
  let x := if copyA D P marked (copies k).val = alpha D P
    then copyB D P marked (copies k).val else copyA D P marked (copies k).val
  let equiv := sourceForestDualEquiv FiniteAvalanches.External.finite_plane_tree_complement
    D P hD marked Q charts finiteFaces
  let color : ReferenceMoment.Forest D P marked → ℝ := fun F =>
    if (StatementTypes.graph D P marked).reaches F.val x (beta D P) then 1 else 0
  have he : (copyA D P marked (copies k).val = alpha D P ∧
      copyB D P marked (copies k).val = x) ∨
      (copyB D P marked (copies k).val = alpha D P ∧
      copyA D P marked (copies k).val = x) := by
    by_cases ha : copyA D P marked (copies k).val = alpha D P
    · exact Or.inl ⟨ha, (if_pos ha).symm⟩
    · exact Or.inr ⟨(copies k).property.resolve_left ha, (if_neg ha).symm⟩
  have hcolor (F : ReferenceMoment.Forest D P marked) :
      color F = J.pathIndicator (equiv F) (vertices 0) (vertices (Fin.last m)) (copies k).val := by
    have h := source_boundary_color_path FiniteAvalanches.External.finite_plane_tree_complement
      D P hD marked Q charts finiteFaces F (copies k).val x he
    rcases hmarked with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · rw [ha, hb] at h
      exact h
    · rw [ha, hb] at h
      exact h.trans (CopiedGraph.pathIndicator_swap J (equiv F)
        (vertices (Fin.last m)) (vertices 0) (copies k).val)
  have hmean : (∑ F : ReferenceMoment.Forest D P marked, color F) /
      (Fintype.card (ReferenceMoment.Forest D P marked) : ℝ) =
      (∑ T : J.SpanningTree,
        J.pathIndicator T (vertices 0) (vertices (Fin.last m)) (copies k).val) /
        (Fintype.card J.SpanningTree : ℝ) := by
    rw [source_forest_uniform_mean FiniteAvalanches.External.finite_plane_tree_complement
      D P hD marked Q charts finiteFaces (Fintype.ofFinite J.SpanningTree) color]
    congr 1
    apply Finset.sum_congr rfl
    intro T _
    rw [hcolor, equiv.apply_symm_apply]
  exact hmean

/-- The literal source color fraction is the characterized source voltage. -/
theorem original_boundary_voltage_eq_tree_average (k : Fin m) :
    let J := sourceDeletedDualGraph D P marked Q charts
    letI : Fintype J.SpanningTree := Fintype.ofFinite J.SpanningTree
    Repair8.voltage D P hD marked
      (if copyA D P marked (copies k).val = alpha D P
        then copyB D P marked (copies k).val else copyA D P marked (copies k).val) =
    (∑ T : J.SpanningTree,
      J.pathIndicator T (vertices 0) (vertices (Fin.last m)) (copies k).val) /
      (Fintype.card J.SpanningTree : ℝ) := by
  let J := sourceDeletedDualGraph D P marked Q charts
  letI : Fintype J.SpanningTree := Fintype.ofFinite J.SpanningTree
  let x := if copyA D P marked (copies k).val = alpha D P
    then copyB D P marked (copies k).val else copyA D P marked (copies k).val
  have hv := (ReferenceMoment.indicator_average_eq_colorMass D P marked x).trans
    (ReferenceMoment.vertexColorMass_eq_voltage D P marked hD x)
  exact hv.symm.trans (original_boundary_color_average_eq_tree_average
    D P hD marked Q charts vertices copies hmarked k)

include hinj hends

/-- The registered whole complementation theorem is applied to this original Q.
Full forest color means and actual signed tree currents give each original Green drop. -/
theorem original_boundary_voltage_eq_green_drop (k : Fin m) :
    let J := sourceDeletedDualGraph D P marked Q charts
    let hc := source_deleted_dual_preconnected_of_classical D P hD hDc hP marked Q charts
      FiniteAvalanches.External.finite_plane_dual_connected
      FiniteAvalanches.External.finite_plane_dual_bond_cycle
    let G := groundedGreen J.left J.right (vertices (Fin.last m)) hc
    Repair8.voltage D P hD marked
      (if copyA D P marked (copies k).val = alpha D P
        then copyB D P marked (copies k).val else copyA D P marked (copies k).val) =
      G (vertices 0) (vertices k.castSucc) - G (vertices 0) (vertices k.succ) := by
  let J := sourceDeletedDualGraph D P marked Q charts
  let hc := source_deleted_dual_preconnected_of_classical D P hD hDc hP marked Q charts
    FiniteAvalanches.External.finite_plane_dual_connected
    FiniteAvalanches.External.finite_plane_dual_bond_cycle
  obtain ⟨B, hpoints, hcurves, hcircle⟩ :=
    original_boundary_disk_drawing D P hD hDc hP marked Q charts vertices hinj copies hends
  exact (original_boundary_voltage_eq_tree_average D P hD marked Q charts
    vertices copies hmarked k).trans
    (boundary_indicator_mean_eq_green_drop J B hc m vertices hinj (fun j => (copies j).val)
      hends hpoints hcurves hcircle k)

/-- The actual alpha1 suffix current is the original off-diagonal Green value.
This holds for every supplied original Q/charts/full face carrier and boundary order. -/
theorem actual_suffixCurrent_eq_original_green (i : Fin (m + 1)) :
    let J := sourceDeletedDualGraph D P marked Q charts
    let hc := source_deleted_dual_preconnected_of_classical D P hD hDc hP marked Q charts
      FiniteAvalanches.External.finite_plane_dual_connected
      FiniteAvalanches.External.finite_plane_dual_bond_cycle
    groundedGreen J.left J.right (vertices (Fin.last m)) hc (vertices 0) (vertices i) =
      suffixCurrent D P hD marked copies i.val := by
  let J := sourceDeletedDualGraph D P marked Q charts
  let hc := source_deleted_dual_preconnected_of_classical D P hD hDc hP marked Q charts
    FiniteAvalanches.External.finite_plane_dual_connected
    FiniteAvalanches.External.finite_plane_dual_bond_cycle
  let G := groundedGreen J.left J.right (vertices (Fin.last m)) hc
  have hsum : suffixCurrent D P hD marked copies i.val =
      ∑ k : Fin m, if i.val ≤ k.val then
        G (vertices 0) (vertices k.castSucc) - G (vertices 0) (vertices k.succ) else 0 := by
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : i.val ≤ k.val
    · simp only [if_pos h]
      exact original_boundary_voltage_eq_green_drop D P hD hDc hP marked Q charts
        vertices hinj copies hends hmarked k
    · simp only [if_neg h]
  have ht := sum_suffix_sub m (fun j => G (vertices 0) (vertices j)) i
  have hg : G (vertices 0) (vertices (Fin.last m)) = 0 := groundedGreen_ground _ _ _ _ _
  rw [hg, sub_zero] at ht
  exact (hsum.trans ht).symm

/-- The correction in the unsymmetrized ground identity is the actual original psi_i. -/
theorem actual_split_inflow_eq_original_green (i : Fin (m + 1)) :
    let J := sourceDeletedDualGraph D P marked Q charts
    let hc := source_deleted_dual_preconnected_of_classical D P hD hDc hP marked Q charts
      FiniteAvalanches.External.finite_plane_dual_connected
      FiniteAvalanches.External.finite_plane_dual_bond_cycle;
    -laplacian (actualSplit D P marked copies i.val).left
      (actualSplit D P marked copies i.val).right (splitVoltage D P hD marked) (.inr true) =
      groundedGreen J.left J.right (vertices (Fin.last m)) hc (vertices 0) (vertices i) := by
  exact (actual_split_inflow D P hD marked copies i.val).trans
    (actual_suffixCurrent_eq_original_green D P hD hDc hP marked Q charts
      vertices hinj copies hends hmarked i).symm

/-- The proved current dictionary supplies the original psi correction, for every trial
and with the beta trial value free. The diagonal Green dictionary is still separate. -/
theorem actual_split_response_sub_original_green_bound (i : Fin (m + 1))
    (f : SplitVertex (alpha D P) → ℝ) (hf0 : f (.inr false) = 0)
    (hf1 : f (.inr true) = 1) :
    let J := sourceDeletedDualGraph D P marked Q charts
    let hc := source_deleted_dual_preconnected_of_classical D P hD hDc hP marked Q charts
      FiniteAvalanches.External.finite_plane_dual_connected
      FiniteAvalanches.External.finite_plane_dual_bond_cycle
    totalResponse D P hD marked copies i.val -
      groundedGreen J.left J.right (vertices (Fin.last m)) hc (vertices 0) (vertices i) ≤
      ∑ e : Copy D P marked,
        (1 - splitVoltage D P hD marked ((actualSplit D P marked copies i.val).left e)) *
        (1 - splitVoltage D P hD marked ((actualSplit D P marked copies i.val).right e)) *
        (f ((actualSplit D P marked copies i.val).left e) -
          f ((actualSplit D P marked copies i.val).right e)) ^ 2 := by
  dsimp only
  rw [actual_suffixCurrent_eq_original_green D P hD hDc hP marked Q charts
    vertices hinj copies hends hmarked i]
  exact actual_split_total_response_bound D P hD marked copies i.val f hf0 hf1

end
end FiniteAvalanches.Electrical.SplitStep
