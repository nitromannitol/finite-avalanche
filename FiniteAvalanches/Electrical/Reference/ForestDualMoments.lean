import FiniteAvalanches.Electrical.Reference.ForestDualDictionary
import FiniteAvalanches.Electrical.Reference.BoundarySum
import FiniteAvalanches.External.PlaneTreeComplement

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeDrawing
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice
open scoped Classical BigOperators
noncomputable section

/-- The full original dart observable is the dual path-contact sum under any complete
boundary enumeration, with the original marked dual endpoints in either orientation. -/
theorem source_forest_contacts_eq_path_sum
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) (finiteFaces : Fintype (Face Q)) :
    letI : Fintype (Face Q) := finiteFaces
    ∀ (m : ℕ) (vertices : Fin (m + 1) → Face Q)
      (copies : Fin m ≃ {e : Copy D P marked //
        copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}),
      (((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices 0 ∧
          (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices (Fin.last m)) ∨
        ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices 0 ∧
          (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices (Fin.last m))) →
    ∀ F : ReferenceMoment.Forest D P marked,
      ReferenceMoment.boundaryContacts D P marked F =
        ∑ i : Fin m, (sourceDeletedDualGraph D P marked Q charts).pathIndicator
          (sourceForestDualEquiv FiniteAvalanches.External.finite_plane_tree_complement
            D P hD marked Q charts finiteFaces F)
          (vertices 0) (vertices (Fin.last m)) (copies i).val := by
  letI : Fintype (Face Q) := finiteFaces
  intro m vertices copies hmarked F
  have hinj : Function.Injective (fun i => (copies i).val.val) := by
    intro i j h
    exact copies.injective (Subtype.ext (Subtype.ext h))
  have hcoverage (e : Copy D P marked) : (∃ i, (copies i).val = e) ↔
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P := by
    constructor
    · rintro ⟨i, rfl⟩
      exact (copies i).property
    · intro he
      obtain ⟨i, hi⟩ := copies.surjective ⟨e, he⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  rw [source_boundary_contact_sum D P marked m (fun i => (copies i).val) hinj hcoverage F]
  apply Finset.sum_congr rfl
  intro i _
  let x := if copyA D P marked (copies i).val = alpha D P
    then copyB D P marked (copies i).val else copyA D P marked (copies i).val
  have he : (copyA D P marked (copies i).val = alpha D P ∧
      copyB D P marked (copies i).val = x) ∨
      (copyB D P marked (copies i).val = alpha D P ∧
      copyA D P marked (copies i).val = x) := by
    by_cases ha : copyA D P marked (copies i).val = alpha D P
    · exact Or.inl ⟨ha, (if_pos ha).symm⟩
    · exact Or.inr ⟨(copies i).property.resolve_left ha, (if_neg ha).symm⟩
  have h := source_boundary_color_path FiniteAvalanches.External.finite_plane_tree_complement
    D P hD marked Q charts finiteFaces F (copies i).val x he
  rcases hmarked with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · rw [ha, hb] at h
    exact h
  · rw [ha, hb] at h
    exact h.trans (CopiedGraph.pathIndicator_swap _ _ _ _ _)

/-- A full finite pushforward law for the original contact observable, retaining both
entire carriers and their denominators. In particular it transports every moment. -/
theorem source_forest_contact_law
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) (finiteFaces : Fintype (Face Q)) :
    letI : Fintype (Face Q) := finiteFaces
    let J := sourceDeletedDualGraph D P marked Q charts
    ∀ treeEnumeration : Fintype J.SpanningTree,
    letI := treeEnumeration
    ∀ (m : ℕ) (vertices : Fin (m + 1) → Face Q)
      (copies : Fin m ≃ {e : Copy D P marked //
        copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}),
      (((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices 0 ∧
          (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices (Fin.last m)) ∨
        ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices 0 ∧
          (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices (Fin.last m))) →
      Fintype.card (ReferenceMoment.Forest D P marked) = Fintype.card J.SpanningTree ∧
      0 < Fintype.card J.SpanningTree ∧
      ∀ f : ℝ → ℝ,
        (∑ F : ReferenceMoment.Forest D P marked,
          f (ReferenceMoment.boundaryContacts D P marked F)) /
          (Fintype.card (ReferenceMoment.Forest D P marked) : ℝ) =
        (∑ T : J.SpanningTree, f (∑ i : Fin m,
          J.pathIndicator T (vertices 0) (vertices (Fin.last m)) (copies i).val)) /
          (Fintype.card J.SpanningTree : ℝ) := by
  letI : Fintype (Face Q) := finiteFaces
  intro J treeEnumeration
  letI := treeEnumeration
  intro m vertices copies hmarked
  let forestDual := sourceForestDualEquiv FiniteAvalanches.External.finite_plane_tree_complement
    D P hD marked Q charts finiteFaces
  have hcard := Fintype.card_congr forestDual
  have hforest : Nonempty (ReferenceMoment.Forest D P marked) := Repair8.forest_nonempty D P hD marked
  have hcount : 0 < Fintype.card J.SpanningTree := by
    rw [← hcard]
    exact Fintype.card_pos_iff.mpr hforest
  refine ⟨hcard, hcount, ?_⟩
  intro f
  rw [source_forest_uniform_mean FiniteAvalanches.External.finite_plane_tree_complement
    D P hD marked Q charts finiteFaces treeEnumeration]
  congr 1
  apply Finset.sum_congr rfl
  intro T _
  rw [source_forest_contacts_eq_path_sum D P hD marked Q charts finiteFaces m vertices copies hmarked,
    forestDual.apply_symm_apply]

/-- Variance transports with the actual original forest mean as its center. -/
theorem source_forest_variance_transport
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) (finiteFaces : Fintype (Face Q)) :
    letI : Fintype (Face Q) := finiteFaces
    let J := sourceDeletedDualGraph D P marked Q charts
    ∀ treeEnumeration : Fintype J.SpanningTree,
    letI := treeEnumeration
    ∀ (m : ℕ) (vertices : Fin (m + 1) → Face Q)
      (copies : Fin m ≃ {e : Copy D P marked //
        copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}),
      (((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices 0 ∧
          (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices (Fin.last m)) ∨
        ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices 0 ∧
          (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices (Fin.last m))) →
      let mean := ReferenceMoment.forestMean D P marked
      let treeMean := (∑ T : J.SpanningTree, ∑ i : Fin m,
        J.pathIndicator T (vertices 0) (vertices (Fin.last m)) (copies i).val) /
        (Fintype.card J.SpanningTree : ℝ)
      mean = treeMean ∧
      (∑ F : ReferenceMoment.Forest D P marked,
        (ReferenceMoment.boundaryContacts D P marked F - mean)^2) /
        (Fintype.card (ReferenceMoment.Forest D P marked) : ℝ) =
      (∑ T : J.SpanningTree, ((∑ i : Fin m,
        J.pathIndicator T (vertices 0) (vertices (Fin.last m)) (copies i).val) - treeMean)^2) /
        (Fintype.card J.SpanningTree : ℝ) := by
  letI : Fintype (Face Q) := finiteFaces
  intro J treeEnumeration
  letI := treeEnumeration
  intro m vertices copies hmarked mean treeMean
  have hlaw := (source_forest_contact_law D P hD marked Q charts finiteFaces
    treeEnumeration m vertices copies hmarked).2.2
  have hmean := hlaw id
  change mean = treeMean at hmean
  refine ⟨hmean, ?_⟩
  have hv := hlaw (fun y => (y - mean)^2)
  calc
    _ = (∑ T : J.SpanningTree, ((∑ i : Fin m,
        J.pathIndicator T (vertices 0) (vertices (Fin.last m)) (copies i).val) - mean)^2) /
        (Fintype.card J.SpanningTree : ℝ) := hv
    _ = _ := congrArg (fun y : ℝ => (∑ T : J.SpanningTree, ((∑ i : Fin m,
        J.pathIndicator T (vertices 0) (vertices (Fin.last m)) (copies i).val) - y)^2) /
        (Fintype.card J.SpanningTree : ℝ)) hmean
end
end FiniteAvalanches.Electrical.LatticeDrawing
