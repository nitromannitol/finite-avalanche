import OriginalStreamApplication
import FiniteAvalanches.Electrical.SplitStep.OriginalAssembly22
import FiniteAvalanches.Electrical.Reference.PathProbabilities

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Electrical.Plane.SourceLattice.ReferenceMoment
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing SplitStep
open scoped Classical BigOperators
noncomputable section

/-- All original copies, the signed boundary means in the coupled forest/tree law,
and the original energy, on the supplied source face carrier and boundary order. -/
theorem boundary_means_on_source_drawing
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (LatticeDrawing.primalGraph D P))
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
        (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices (Fin.last m))) :
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
  intro J hc G phi F
  letI : Fintype J.SpanningTree := Fintype.ofFinite J.SpanningTree
  obtain ⟨sigma, hsigma, hheight⟩ := LovaszApplication.constructed_original_height_eq_neg_green
    D P hD marked Q charts (vertices 0) (vertices (Fin.last m)) hc hmarked
  have hstream := (LovaszStream.originalStream_spec D P hD marked Q charts).1
  have hconjugate (e : Copy D P marked) :
      |G (vertices 0) (J.left e) - G (vertices 0) (J.right e)| =
        |phi (copyA D P marked e) - phi (copyB D P marked e)| := by
    have hd : G (vertices 0) (J.left e) - G (vertices 0) (J.right e) =
        sigma * (LovaszStream.originalStream D P hD marked Q charts (J.right e) -
          LovaszStream.originalStream D P hD marked Q charts (J.left e)) := by
      have hl := hheight (J.left e)
      have hr := hheight (J.right e)
      dsimp only [G] at hl hr ⊢
      linarith only [hl, hr]
    rw [hstream e] at hd
    rw [hd, abs_mul]
    rcases hsigma with hsigma | hsigma <;>
      simp only [hsigma, abs_one, abs_neg, one_mul] <;> rfl
  have hboundary (i : Fin m) := original_boundary_voltage_eq_green_drop
    D P hD hDc hP marked Q charts vertices hinj copies hends hmarked i
  have hsum := (source_path_probability_bounds D P hD hDc hP marked Q charts
    finiteFaces m vertices hinj copies hends hmarked).2
  have ht := sum_suffix_sub m (fun j => G (vertices 0) (vertices j)) (0 : Fin (m + 1))
  simp only [Fin.val_zero, Nat.zero_le, if_true] at ht
  have hg : G (vertices 0) (vertices (Fin.last m)) = 0 :=
    groundedGreen_ground J.left J.right (vertices (Fin.last m)) hc (vertices 0)
  rw [hg, sub_zero] at ht
  have hmean : ReferenceMoment.forestMean D P marked = G (vertices 0) (vertices 0) :=
    hsum.symm.trans ht
  refine ⟨hconjugate, ?_, hmean,
    hmean.symm.trans (ReferenceMoment.mean_eq_energy D P marked hD)⟩
  intro i x I
  have hv := (ReferenceMoment.indicator_average_eq_colorMass D P marked x).trans
    (ReferenceMoment.vertexColorMass_eq_voltage D P marked hD x)
  exact ⟨(hboundary i).symm, hv.symm,
    original_boundary_color_average_eq_tree_average D P hD marked Q charts
      vertices copies hmarked i⟩

end
end FiniteAvalanches.Electrical.Plane.SourceLattice.ReferenceMoment

#print axioms FiniteAvalanches.Electrical.Plane.SourceLattice.ReferenceMoment.boundary_means_on_source_drawing
