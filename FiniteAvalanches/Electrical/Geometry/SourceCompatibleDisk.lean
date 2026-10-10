import FiniteAvalanches.Electrical.Geometry.ActualSourceDiskDrawingConsumer

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeDrawing
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeCell
open ComplementFaces PunctureTransport IncidenceApplication
open scoped Classical
noncomputable section

/-- Every original all-face dual drawing admits a same-copy disk realization of any
simple enumeration of the whole retained alpha boundary. -/
theorem source_compatible_path_disk
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) (finiteFaces : Fintype (Face Q)) :
    letI : Fintype (Face Q) := finiteFaces
    ∀ (m : ℕ) (vertices : Fin (m + 1) → Face Q), Function.Injective vertices →
    ∀ copies : Fin m → Copy D P marked,
      (∀ i, copyA D P marked (copies i) = alpha D P ∨
        copyB D P marked (copies i) = alpha D P) →
      (∀ i,
        ((sourceDeletedDualGraph D P marked Q charts).left (copies i) = vertices i.castSucc ∧
          (sourceDeletedDualGraph D P marked Q charts).right (copies i) = vertices i.succ) ∨
        ((sourceDeletedDualGraph D P marked Q charts).right (copies i) = vertices i.castSucc ∧
          (sourceDeletedDualGraph D P marked Q charts).left (copies i) = vertices i.succ)) →
      ∃ diskDrawing : Drawing (sourceDeletedDualGraph D P marked Q charts),
        (∀ F, diskDrawing.point F ∈ disk) ∧
        (∀ e t, diskDrawing.curve e t ∈ disk) ∧
        (∀ i t, diskDrawing.curve (copies i) t ∈ circle) := by
  letI : Fintype (Face Q) := finiteFaces
  intro m vertices hinj copies hboundary hends
  letI : Nonempty (PrimalCopy D P) := ⟨markedPrimal D P marked⟩
  obtain ⟨finiteFaces', hdual⟩ := FiniteAvalanches.External.finite_plane_geometric_dual
    (primalGraph D P) Q charts (primal_preconnected D P hD marked)
  have hfinite : finiteFaces' = finiteFaces := Subsingleton.elim _ _
  subst finiteFaces'
  change ∃ fullDual : Drawing (sourceDualGraph D P Q charts),
    ∃ dualCharts : ∀ e, EdgeChart fullDual e,
    ∃ vertexFaces : Vertex D P ≃ Face fullDual, _ at hdual
  obtain ⟨fullDual, dualCharts, vertexFaces, _hpoint, hvertex, _hcross,
    _hparts, _hlocal, horient⟩ := hdual
  let R := deleteMarkedDualDrawing D P marked Q charts fullDual
  have htrace : drawingTrace R ⊆ drawingTrace fullDual := by
    rintro z (⟨v, hv⟩ | hz)
    · exact Or.inl ⟨v, hv⟩
    · obtain ⟨e, t, ht⟩ := Set.mem_iUnion.mp hz
      exact Or.inr (Set.mem_iUnion.mpr ⟨retainedPrimal D P marked e, t, ht⟩)
  have hsafe : Q.point (alpha D P) ∉ drawingTrace fullDual := (hvertex _).1
  let merged := faceAt R (Q.point (alpha D P)) (fun h => hsafe (htrace h))
  have hregion : faceRegion fullDual (vertexFaces (alpha D P)) ⊆ faceRegion R merged := by
    have hs := faceRegion_subset_of_trace_subset fullDual R htrace _ hsafe
    have he := (hvertex (alpha D P)).2
    change faceAt fullDual (Q.point (alpha D P)) hsafe = vertexFaces (alpha D P) at he
    rw [he] at hs
    exact hs
  have hfront (i : Fin m) : Set.range (R.curve (copies i)) ⊆ frontier (faceRegion R merged) := by
    have hne := path_copy_nonloop m vertices hinj copies hends i
    obtain ⟨hpositive, hnegative⟩ := FiniteAvalanches.External.plane_edge_chart_incidence
      (sourceDualGraph D P Q charts) fullDual (retainedPrimal D P marked (copies i))
      (dualCharts _) hne
    have hwhole : Set.range (fullDual.curve (retainedPrimal D P marked (copies i))) ⊆
        closure (faceRegion fullDual (vertexFaces (alpha D P))) := by
      rcases hboundary i with ha | hb
      · have he : positiveChartFace fullDual (retainedPrimal D P marked (copies i))
            (dualCharts _) = vertexFaces (alpha D P) :=
          (horient (retainedPrimal D P marked (copies i))).1.trans (congrArg vertexFaces ha)
        exact he ▸ hpositive
      · have he : negativeChartFace fullDual (retainedPrimal D P marked (copies i))
            (dualCharts _) = vertexFaces (alpha D P) :=
          (horient (retainedPrimal D P marked (copies i))).2.trans (congrArg vertexFaces hb)
        exact he ▸ hnegative
    rintro z ⟨t, rfl⟩
    apply mem_frontier_of_mem_trace R merged _
    · exact Or.inr (Set.mem_iUnion.mpr ⟨copies i, Set.mem_range_self t⟩)
    · exact closure_mono hregion (hwhole (Set.mem_range_self t))
  obtain ⟨pole, hpole, _hpinside, c, _hformula, redrawn, _hnewp, hnewc,
    faces, hregions, hclosures, _hincidences, _hcurveclosures, hunbounded⟩ :=
    FiniteAvalanches.External.plane_punctured_face_transport
      (sourceDualGraph D P Q charts) (sourceDeletedDualGraph D P marked Q charts)
      fullDual (retainedPrimal D P marked) (retainedPrimal_injective D P marked)
      (fun _ => rfl) (fun _ => rfl) merged
  let R' := deleteMarkedDualDrawing D P marked Q charts redrawn
  have hnewboundary (i : Fin m) (t : ArcParameter) :
      R'.curve (copies i) t ∈ frontier (faceRegion R' (faces merged)) := by
    have hoff : fullDual.curve (retainedPrimal D P marked (copies i)) t ≠ pole := by
      intro heq
      apply hpole
      exact heq ▸ (Or.inr (Set.mem_iUnion.mpr ⟨_, Set.mem_range_self t⟩))
    have hb := (frontier_transport R R' merged (faces merged) _ _
      (hregions merged ⟨_, hoff⟩) (hclosures merged ⟨_, hoff⟩)).mp
      (hfront i (Set.mem_range_self t))
    change redrawn.curve _ t ∈ _
    rw [hnewc]
    exact hb
  have hconn := source_deleted_dual_preconnected_of_classical D P hD hDc hP marked Q charts
    FiniteAvalanches.External.finite_plane_dual_connected
    FiniteAvalanches.External.finite_plane_dual_bond_cycle
  exact FiniteAvalanches.External.outer_face_simple_path_disk_redrawing
    (sourceDeletedDualGraph D P marked Q charts) R' hconn m vertices hinj copies hends
    (faces merged) hunbounded hnewboundary
end
end FiniteAvalanches.Electrical.LatticeDrawing
