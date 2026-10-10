import FiniteAvalanches.Electrical.Geometry.SourceDualFaceMerger

/-! Ordinary consequences of whole-edge incidence in actual complement faces. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.IncidenceApplication
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST

variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- The existing Drawing fields give a closed embedded arc for every nonloop copy. -/
theorem nonloop_curve_isClosedEmbedding (R : Drawing J) (e : E)
    (hne : J.left e ≠ J.right e) : Topology.IsClosedEmbedding (R.curve e) :=
  (R.continuous e).isClosedEmbedding (R.nonloop_curve_injective e hne)

/-- A drawn point in a face closure lies on its frontier, since the face avoids the trace. -/
theorem mem_frontier_of_mem_trace (R : Drawing J) (F : Face R) (z : Plane)
    (hz : z ∈ drawingTrace R) (hc : z ∈ closure (faceRegion R F)) :
    z ∈ frontier (faceRegion R F) := by
  rw [frontier_eq_closure_inter_closure]
  refine ⟨hc, subset_closure ?_⟩
  intro hf
  exact hf.1 hz

omit [Fintype V] [Fintype E] in
/-- A simple copied path has no loop edges; this is derived from its actual endpoints. -/
theorem path_copy_nonloop (m : ℕ) (vertices : Fin (m + 1) → V)
    (hinj : Function.Injective vertices) (copies : Fin m → E)
    (hends : ∀ i : Fin m,
      (J.left (copies i) = vertices i.castSucc ∧ J.right (copies i) = vertices i.succ) ∨
      (J.right (copies i) = vertices i.castSucc ∧ J.left (copies i) = vertices i.succ))
    (i : Fin m) : J.left (copies i) ≠ J.right (copies i) := by
  intro he
  have hi : vertices i.castSucc = vertices i.succ := by
    rcases hends i with h | h
    · exact h.1.symm.trans (he.trans h.2)
    · exact h.1.symm.trans (he.symm.trans h.2)
  have hv := congrArg Fin.val (hinj hi)
  simp only [Fin.val_castSucc, Fin.val_succ] at hv
  omega

/-- Every vertex of a positive-length copied path is an endpoint of a path curve. -/
theorem path_vertices_mem_frontier (R : Drawing J) (F : Face R) (m : ℕ)
    (hm : 0 < m) (vertices : Fin (m + 1) → V) (copies : Fin m → E)
    (hends : ∀ i : Fin m,
      (J.left (copies i) = vertices i.castSucc ∧ J.right (copies i) = vertices i.succ) ∨
      (J.right (copies i) = vertices i.castSucc ∧ J.left (copies i) = vertices i.succ))
    (hcurves : ∀ i, Set.range (R.curve (copies i)) ⊆ frontier (faceRegion R F)) :
    ∀ k, R.point (vertices k) ∈ frontier (faceRegion R F) := by
  have endpoints (i : Fin m) :
      R.point (vertices i.castSucc) ∈ frontier (faceRegion R F) ∧
      R.point (vertices i.succ) ∈ frontier (faceRegion R F) := by
    have hs := hcurves i ⟨⟨0, by constructor <;> norm_num⟩, R.start _⟩
    have ht := hcurves i ⟨⟨1, by constructor <;> norm_num⟩, R.finish _⟩
    rcases hends i with h | h
    · exact ⟨h.1 ▸ hs, h.2 ▸ ht⟩
    · exact ⟨h.1 ▸ ht, h.2 ▸ hs⟩
  intro k
  refine Fin.cases ?_ (fun i => (endpoints i).2) k
  exact (endpoints ⟨0, hm⟩).1

end FiniteAvalanches.Electrical.IncidenceApplication
