import FiniteAvalanches.Electrical.Geometry.PunctureTransport
import FiniteAvalanches.Electrical.Geometry.SourceDeletedDualPointwise
import FiniteAvalanches.External.PlaneEdgeChartIncidence
import FiniteAvalanches.External.PlanePuncturedFaceTransport
import FiniteAvalanches.External.PlaneDualConnected
import FiniteAvalanches.External.PlaneDualBondCycle
import FiniteAvalanches.External.OuterFaceRedrawing

set_option autoImplicit false

namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing
open DrawingContraction ComplementFaces IncidenceApplication PunctureTransport
open scoped Classical
noncomputable section

/-- For the supplied original Q and supplied original boundary order, derive a disk
drawing of the identical dual copied graph. This is used only for the combinatorial
signed-path identity, and asserts no primal-incidence preservation of the disk drawing. -/
theorem original_boundary_disk_drawing
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) [sourceFaces : Fintype (Face Q)]
    {m : ℕ} (vertices : Fin (m + 1) → Face Q) (hinj : Function.Injective vertices)
    (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P})
    (hends : ∀ k : Fin m,
      ((sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.castSucc ∧
        (sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.succ) ∨
      ((sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.castSucc ∧
        (sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.succ)) :
    ∃ B : Drawing (sourceDeletedDualGraph D P marked Q charts),
      (∀ x, B.point x ∈ disk) ∧ (∀ e t, B.curve e t ∈ disk) ∧
      (∀ k t, B.curve (copies k).val t ∈ circle) := by
  letI : Nonempty (LatticeDrawing.PrimalCopy D P) := ⟨markedPrimal D P marked⟩
  obtain ⟨finiteFaces, hdual⟩ := FiniteAvalanches.External.finite_plane_geometric_dual
    (primalGraph D P) Q charts (primal_preconnected D P hD marked)
  have henum : finiteFaces = sourceFaces := Subsingleton.elim _ _
  subst finiteFaces
  obtain ⟨dual, dualCharts, vertexFaces, hpoint, hvertex, hcross,
    _hparts, _hlocal, horient⟩ := hdual
  change Drawing (sourceDualGraph D P Q charts) at dual
  let R := deleteMarkedDualDrawing D P marked Q charts dual
  have htrace : drawingTrace R ⊆ drawingTrace dual := by
    rintro z (⟨v, hv⟩ | hz)
    · exact Or.inl ⟨v, hv⟩
    · obtain ⟨e, t, ht⟩ := Set.mem_iUnion.mp hz
      exact Or.inr (Set.mem_iUnion.mpr ⟨retainedPrimal D P marked e, t, ht⟩)
  have hoff (s : ArcParameter) : Q.curve (markedPrimal D P marked) s ∉ drawingTrace R := by
    rintro (⟨v, hv⟩ | hz)
    · apply (hpoint v).1
      exact Or.inr (Set.mem_iUnion.mpr ⟨markedPrimal D P marked, s, hv.symm⟩)
    · obtain ⟨e, t, ht⟩ := Set.mem_iUnion.mp hz
      have he := (hcross (markedPrimal D P marked) (retainedPrimal D P marked e) s t).mp ht.symm
      exact retainedPrimal_ne_marked D P marked e he.1.symm
  obtain ⟨merged, hinside, _, _⟩ := DeletedArc.common_face R
    (Q.curve (markedPrimal D P marked)) (Q.continuous _) (fun t _ _ => hoff t)
  have hall : Set.range (Q.curve (markedPrimal D P marked)) ⊆ faceRegion R merged := by
    have hwhole := range_subset_faceAt R (Q.curve (markedPrimal D P marked))
      (Q.continuous _) hoff
    have hmid := hinside ⟨1/2, by constructor <;> norm_num⟩ (by norm_num) (by norm_num)
    have heq := face_eq_of_mem R _ merged _
      (hwhole (Set.mem_range_self ⟨1/2, by constructor <;> norm_num⟩)) hmid
    exact heq ▸ hwhole
  have halpha : Q.point (alpha D P) ∈ faceRegion R merged := by
    have hs := hall ⟨⟨0, by constructor <;> norm_num⟩, Q.start _⟩
    have ht := hall ⟨⟨1, by constructor <;> norm_num⟩, Q.finish _⟩
    exact marked.property.elim (fun h => h.1 ▸ hs) (fun h => h.2 ▸ ht)
  have hregionAlpha : faceRegion dual (vertexFaces (alpha D P)) ⊆ faceRegion R merged := by
    obtain ⟨ho, he⟩ := hvertex (alpha D P)
    have hsub := faceRegion_subset_of_trace_subset dual R htrace (Q.point (alpha D P)) ho
    change faceAt dual (Q.point (alpha D P)) ho = vertexFaces (alpha D P) at he
    rw [he] at hsub
    have hmerge := face_eq_of_mem R _ merged (Q.point (alpha D P))
      (mem_faceAt R _ (fun h => ho (htrace h))) halpha
    exact hmerge ▸ hsub
  have hboundary (k : Fin m) : Set.range (R.curve (copies k).val) ⊆
      frontier (faceRegion R merged) := by
    have hn := path_copy_nonloop m vertices hinj (fun j => (copies j).val) hends k
    obtain ⟨hpositive, hnegative⟩ := FiniteAvalanches.External.plane_edge_chart_incidence
      (sourceDualGraph D P Q charts) dual (retainedPrimal D P marked (copies k).val)
      (dualCharts _) hn
    have hwhole : Set.range (dual.curve (retainedPrimal D P marked (copies k).val)) ⊆
        closure (faceRegion dual (vertexFaces (alpha D P))) := by
      rcases (copies k).property with ha | hb
      · have ho := (horient (retainedPrimal D P marked (copies k).val)).1
        have hpositive' := ho ▸ hpositive
        change Set.range (dual.curve (retainedPrimal D P marked (copies k).val)) ⊆
          closure (faceRegion dual (vertexFaces (copyA D P marked (copies k).val))) at hpositive'
        exact Eq.mp (congrArg (fun v : Vertex D P =>
          Set.range (dual.curve (retainedPrimal D P marked (copies k).val)) ⊆
            closure (faceRegion dual (vertexFaces v))) ha) hpositive'
      · have ho := (horient (retainedPrimal D P marked (copies k).val)).2
        have hnegative' := ho ▸ hnegative
        change Set.range (dual.curve (retainedPrimal D P marked (copies k).val)) ⊆
          closure (faceRegion dual (vertexFaces (copyB D P marked (copies k).val))) at hnegative'
        exact Eq.mp (congrArg (fun v : Vertex D P =>
          Set.range (dual.curve (retainedPrimal D P marked (copies k).val)) ⊆
            closure (faceRegion dual (vertexFaces v))) hb) hnegative'
    rintro z ⟨t, rfl⟩
    apply mem_frontier_of_mem_trace R merged _
    · exact Or.inr (Set.mem_iUnion.mpr ⟨(copies k).val, Set.mem_range_self t⟩)
    · exact closure_mono hregionAlpha (hwhole (Set.mem_range_self t))
  obtain ⟨p, hpole, _hpinside, c, _hformula, redrawn, _hnewp, hnewc,
    faces, hregions, hclosures, _hincidences, _hcurveclosures, hunbounded⟩ :=
    FiniteAvalanches.External.plane_punctured_face_transport (sourceDualGraph D P Q charts)
      (sourceDeletedDualGraph D P marked Q charts) dual
      (retainedPrimal D P marked) (retainedPrimal_injective D P marked)
      (fun _ => rfl) (fun _ => rfl) merged
  let R' := deleteMarkedDualDrawing D P marked Q charts redrawn
  have hnewboundary (k : Fin m) (t : ArcParameter) :
      R'.curve (copies k).val t ∈ frontier (faceRegion R' (faces merged)) := by
    have hoff' : dual.curve (retainedPrimal D P marked (copies k).val) t ≠ p := by
      intro heq
      apply hpole
      exact heq ▸ (Or.inr (Set.mem_iUnion.mpr
        ⟨retainedPrimal D P marked (copies k).val, Set.mem_range_self t⟩))
    have hb := (frontier_transport R R' merged (faces merged) _ _
      (hregions merged ⟨_, hoff'⟩) (hclosures merged ⟨_, hoff'⟩)).mp
      (hboundary k (Set.mem_range_self t))
    change redrawn.curve _ t ∈ _
    rw [hnewc]
    exact hb
  exact FiniteAvalanches.External.outer_face_simple_path_disk_redrawing
    (sourceDeletedDualGraph D P marked Q charts) R'
    (source_deleted_dual_preconnected_of_classical D P hD hDc hP marked Q charts
      FiniteAvalanches.External.finite_plane_dual_connected
      FiniteAvalanches.External.finite_plane_dual_bond_cycle)
    m vertices hinj (fun k => (copies k).val) hends (faces merged) hunbounded hnewboundary

end
end FiniteAvalanches.Electrical.SplitStep
