import FiniteAvalanches.Electrical.PairContact.ActualSourceTreeTwoContact
import FiniteAvalanches.Electrical.Reference.ForestDualDictionary
import FiniteAvalanches.Electrical.Reference.BoundarySum

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeDrawing
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeCell
open scoped Classical BigOperators
noncomputable section

/-- One original source geometry supports the complete forest dictionary and uniform products. -/
theorem actual_source_forest_dual_dictionary_of_tree_complement
    (hstandard : (∀ {V E : Type} [finiteV : Fintype V] [finiteE : Fintype E]
    (G : FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph V E)
    (Q : @FiniteAvalanches.Electrical.StatementGeometry.Drawing V E finiteV finiteE G)
    (charts : ∀ e, FiniteAvalanches.Electrical.Source.EdgeChart Q e),
  (Set.univ : Set V).Nonempty →
  (∀ x y, G.reaches Finset.univ x y) →
  ∀ finiteFaces : Fintype (FiniteAvalanches.Electrical.BSST.Face Q),
    letI : Fintype (FiniteAvalanches.Electrical.BSST.Face Q) := finiteFaces
    ∀ S : Finset E,
      ((Set.univ : Set V).Nonempty ∧ (∀ x y, G.reaches S x y) ∧
        ∀ e ∈ S, ¬G.reaches (S.erase e) (G.left e) (G.right e)) ↔
      ((Set.univ : Set (FiniteAvalanches.Electrical.BSST.Face Q)).Nonempty ∧
        (∀ x y, (⟨fun e => FiniteAvalanches.Electrical.BSST.negativeChartFace Q e (charts e),
          fun e => FiniteAvalanches.Electrical.BSST.positiveChartFace Q e (charts e)⟩ :
          FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
            (FiniteAvalanches.Electrical.BSST.Face Q) E).reaches Sᶜ x y) ∧
        ∀ e ∈ Sᶜ, ¬(⟨fun e => FiniteAvalanches.Electrical.BSST.negativeChartFace Q e (charts e),
          fun e => FiniteAvalanches.Electrical.BSST.positiveChartFace Q e (charts e)⟩ :
          FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
            (FiniteAvalanches.Electrical.BSST.Face Q) E).reaches
          (Sᶜ.erase e)
          (FiniteAvalanches.Electrical.BSST.negativeChartFace Q e (charts e))
          (FiniteAvalanches.Electrical.BSST.positiveChartFace Q e (charts e)))))
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
  obtain ⟨q, hq, Q, hp, hc, charts, finiteFaces, hgeometry⟩ :=
    actual_source_deleted_dual_tree_two_contact D P hD hDc hP marked
  letI : Fintype (Face Q) := finiteFaces
  let J := sourceDeletedDualGraph D P marked Q charts
  letI : Fintype J.SpanningTree := Fintype.ofFinite J.SpanningTree
  obtain ⟨m, hm, vertices, hinj, copies, hcopyinj, hcoverage, hends, hnonmarked,
    hmarked, hconn, hreach, Hstar, outerFace, hunbounded, htrace,
    diskDrawing, hdiskPoints, hdiskCurves, hcircle, hwholeCircle,
    θ, hmono, hspan, hangles, hcount, hcountReal, hformula⟩ := hgeometry
  let forestDual := sourceForestDualEquiv hstandard D P hD marked Q charts finiteFaces
  let indicator : ReferenceMoment.Forest D P marked → Fin m → ℝ := fun F i =>
    if (StatementTypes.graph D P marked).reaches F.val
      (if copyA D P marked (copies i) = alpha D P then copyB D P marked (copies i)
        else copyA D P marked (copies i)) (beta D P) then 1 else 0
  have hcolor (F : ReferenceMoment.Forest D P marked) (i : Fin m) :
      indicator F i = J.pathIndicator (forestDual F) (vertices 0)
        (vertices (Fin.last m)) (copies i) := by
    have hi := (hcoverage (copies i)).mp ⟨i, rfl⟩
    let x := if copyA D P marked (copies i) = alpha D P
      then copyB D P marked (copies i) else copyA D P marked (copies i)
    have he : (copyA D P marked (copies i) = alpha D P ∧ copyB D P marked (copies i) = x) ∨
        (copyB D P marked (copies i) = alpha D P ∧ copyA D P marked (copies i) = x) := by
      by_cases ha : copyA D P marked (copies i) = alpha D P
      · exact Or.inl ⟨ha, (if_pos ha).symm⟩
      · exact Or.inr ⟨hi.resolve_left ha, (if_neg ha).symm⟩
    have h := source_boundary_color_path hstandard D P hD marked Q charts finiteFaces F (copies i) x he
    rcases hmarked with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · rw [ha, hb] at h
      exact h
    · rw [ha, hb] at h
      exact h.trans (CopiedGraph.pathIndicator_swap J (forestDual F)
        (vertices (Fin.last m)) (vertices 0) (copies i))
  have hmean := source_forest_uniform_mean hstandard D P hD marked Q charts finiteFaces
    (Fintype.ofFinite J.SpanningTree)
  have hY (F : ReferenceMoment.Forest D P marked) :
      ReferenceMoment.boundaryContacts D P marked F =
        ∑ i : Fin m, J.pathIndicator (forestDual F) (vertices 0)
          (vertices (Fin.last m)) (copies i) :=
    (source_boundary_contact_sum D P marked m copies hcopyinj hcoverage F).trans
      (Finset.sum_congr rfl (fun i _ => hcolor F i))
  have hYmean : ReferenceMoment.forestMean D P marked =
      (∑ T : J.SpanningTree, ∑ i : Fin m,
        J.pathIndicator T (vertices 0) (vertices (Fin.last m)) (copies i)) /
        (Fintype.card J.SpanningTree : ℝ) := by
    unfold ReferenceMoment.forestMean
    rw [hmean (ReferenceMoment.boundaryContacts D P marked)]
    congr 1
    apply Finset.sum_congr rfl
    intro T _
    rw [hY, forestDual.apply_symm_apply]
  have hproducts (indices : Finset (Fin m)) :
      (∑ F : ReferenceMoment.Forest D P marked, ∏ i ∈ indices, indicator F i) /
        (Fintype.card (ReferenceMoment.Forest D P marked) : ℝ) =
      (∑ T : J.SpanningTree, ∏ i ∈ indices,
        J.pathIndicator T (vertices 0) (vertices (Fin.last m)) (copies i)) /
        (Fintype.card J.SpanningTree : ℝ) := by
    rw [hmean (fun F => ∏ i ∈ indices, indicator F i)]
    congr 1
    apply Finset.sum_congr rfl
    intro T _
    apply Finset.prod_congr rfl
    intro i _
    rw [hcolor, forestDual.apply_symm_apply]
  have hpairs (i j : Fin m) :
      (∑ F : ReferenceMoment.Forest D P marked, indicator F i * indicator F j) /
        (Fintype.card (ReferenceMoment.Forest D P marked) : ℝ) =
      (∑ T : J.SpanningTree,
        J.pathIndicator T (vertices 0) (vertices (Fin.last m)) (copies i) *
        J.pathIndicator T (vertices 0) (vertices (Fin.last m)) (copies j)) /
        (Fintype.card J.SpanningTree : ℝ) := by
    rw [hmean (fun F => indicator F i * indicator F j)]
    congr 1
    apply Finset.sum_congr rfl
    intro T _
    rw [hcolor, hcolor, forestDual.apply_symm_apply]
  have hcopies (F : ReferenceMoment.Forest D P marked) :
      (forestDual F).val = F.valᶜ := by
    convert sourceForestDualEquiv_copies hstandard D P hD marked Q charts finiteFaces F using 1
    ext e
    simp only [Finset.mem_compl]
  refine ⟨q, hq, Q, hp, hc, charts, finiteFaces, ?_⟩
  refine ⟨m, hm, vertices, hinj, copies, ?_⟩
  refine ⟨hcopyinj, hcoverage, hends, hnonmarked, hmarked, hconn, ?_⟩
  refine ⟨hreach, Hstar, outerFace, hunbounded, htrace, diskDrawing, ?_⟩
  refine ⟨hdiskPoints, hdiskCurves, hcircle, hwholeCircle, θ, hmono, hspan, hangles, ?_⟩
  exact ⟨hcount, hcountReal, forestDual,
    hcopies,
    Fintype.card_congr forestDual,
    hcolor, hY, hYmean, hproducts, hpairs, hformula⟩

end
end FiniteAvalanches.Electrical.LatticeDrawing
