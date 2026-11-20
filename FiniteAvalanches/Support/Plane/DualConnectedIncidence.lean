import FiniteAvalanches.Support.Plane.DualConnected
import FiniteAvalanches.Support.Plane.GeometricDual

/-!
# Dual connectivity from face incidence

Finite face closures cover the plane. If every face incident to an edge interior
is one of its two chart faces, closures belonging to different dual components
can meet only at vertices. Removing the vertices leaves a connected set, so the
dual has just one component.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Source BSST Set
open scoped Classical

noncomputable section

variable {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
variable {J : CopiedGraph V E}

omit [Nonempty E] in
/-- The two chart faces of an edge belong to the same component of the dual. -/
theorem chartFaces_connectedComponent_eq (D : Drawing J) (charts : ∀ e, EdgeChart D e)
    (e : E) :
    (chartDualGraph D charts).connectedComponentMk (positiveChartFace D e (charts e)) =
      (chartDualGraph D charts).connectedComponentMk (negativeChartFace D e (charts e)) := by
  by_cases h : positiveChartFace D e (charts e) = negativeChartFace D e (charts e)
  · rw [h]
  · apply SimpleGraph.ConnectedComponent.sound
    apply SimpleGraph.Adj.reachable
    exact ⟨h, e, Or.inr ⟨rfl, rfl⟩⟩

/-- Interior face incidence forces the chart dual to be connected. -/
theorem chartDualGraph_preconnected_of_interior_incidence
    (D : Drawing J) (charts : ∀ e, EdgeChart D e)
    (hinc : ∀ (F : Face D) (e : E) (t : ArcParameter),
      0 < t.val → t.val < 1 → D.curve e t ∈ closure (faceRegion D F) →
      F = positiveChartFace D e (charts e) ∨ F = negativeChartFace D e (charts e)) :
    (chartDualGraph D charts).Preconnected := by
  letI : Finite (Face D) := finite_faces_of_interior_incidence D charts
    (fun F e t ht0 ht1 ht => hinc F e t ht0 ht1 (frontier_subset_closure ht))
  let label := (chartDualGraph D charts).connectedComponentMk
  have hmeet : ∀ {z : Plane}, z ∉ range D.point → ∀ F G : Face D,
      z ∈ closure (faceRegion D F) → z ∈ closure (faceRegion D G) →
      label F = label G := by
    intro z hz F G hF hG
    by_cases ht : z ∈ drawingTrace D
    · rcases ht with hv | he
      · exact (hz hv).elim
      · obtain ⟨e, t, ht⟩ := mem_iUnion.mp he
        have ht0 : 0 < t.val := by
          by_contra h
          have h0 : t.val = 0 := le_antisymm (le_of_not_gt h) t.property.1
          have ht' : t = ⟨0, by constructor <;> norm_num⟩ := Subtype.ext h0
          apply hz
          refine ⟨J.left e, ?_⟩
          rw [← ht, ht', D.start]
        have ht1 : t.val < 1 := by
          by_contra h
          have h1 : t.val = 1 := le_antisymm t.property.2 (le_of_not_gt h)
          have ht' : t = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext h1
          apply hz
          refine ⟨J.right e, ?_⟩
          rw [← ht, ht', D.finish]
        have hF' := hinc F e t ht0 ht1 (ht ▸ hF)
        have hG' := hinc G e t ht0 ht1 (ht ▸ hG)
        have hside := chartFaces_connectedComponent_eq D charts e
        rcases hF' with hF' | hF' <;> rcases hG' with hG' | hG' <;>
          simp only [hF', hG', label, hside]
    · have hF' := mem_faceRegion_of_mem_closure D F ht hF
      have hG' := mem_faceRegion_of_mem_closure D G ht hG
      have heq : F = G := by
        rcases hF' with ⟨h1, h1'⟩
        rcases hG' with ⟨h2, h2'⟩
        exact h1'.symm.trans h2'
      rw [heq]
  have hcover : ∀ z : Plane, ∃ F : Face D, z ∈ closure (faceRegion D F) := by
    have hfaces : (⋃ F : Face D, faceRegion D F) = (drawingTrace D)ᶜ := by
      ext z
      constructor
      · intro hz
        obtain ⟨F, hF⟩ := mem_iUnion.mp hz
        exact hF.1
      · intro hz
        exact mem_iUnion.mpr ⟨ConnectedComponents.mk ⟨z, hz⟩, hz, rfl⟩
    intro z
    have hdense : Dense (drawingTrace D)ᶜ :=
      interior_eq_empty_iff_dense_compl.mp (drawingTrace_interior_eq_empty D)
    have hz : z ∈ closure (⋃ F : Face D, faceRegion D F) := by
      rw [hfaces]
      exact hdense z
    rw [closure_iUnion_of_finite] at hz
    exact mem_iUnion.mp hz
  intro F G
  apply SimpleGraph.ConnectedComponent.exact
  by_contra hFG
  let A : Set Plane := ⋃ F' : {H : Face D // label H = label F},
    closure (faceRegion D F'.val)
  let B : Set Plane := ⋃ F' : {H : Face D // label H ≠ label F},
    closure (faceRegion D F'.val)
  have hA : IsClosed A := isClosed_iUnion_of_finite (fun _ => isClosed_closure)
  have hB : IsClosed B := isClosed_iUnion_of_finite (fun _ => isClosed_closure)
  let S : Set Plane := (range D.point)ᶜ
  have hS : IsPreconnected S :=
    (LatticeProb.PlaneTopology.isPathConnected_compl_range D.point).isConnected.isPreconnected
  have hAB : ∀ z ∈ S, ¬ (z ∈ A ∧ z ∈ B) := by
    intro z hz ⟨ha, hb⟩
    obtain ⟨a, ha⟩ := mem_iUnion.mp ha
    obtain ⟨b, hb⟩ := mem_iUnion.mp hb
    exact b.property ((hmeet hz a.val b.val ha hb).symm.trans a.property)
  have hSA : S ⊆ Bᶜ ∪ Aᶜ := by
    intro z hz
    by_cases h : z ∈ B
    · exact Or.inr (fun ha => hAB z hz ⟨ha, h⟩)
    · exact Or.inl h
  obtain ⟨x, hx⟩ := (faceRegion_isConnected D F).nonempty
  obtain ⟨y, hy⟩ := (faceRegion_isConnected D G).nonempty
  have hxS : x ∈ S := fun hv => hx.1 (Or.inl hv)
  have hyS : y ∈ S := fun hv => hy.1 (Or.inl hv)
  have hxA : x ∈ A := mem_iUnion.mpr ⟨⟨F, rfl⟩, subset_closure hx⟩
  have hyB : y ∈ B := mem_iUnion.mpr ⟨⟨G, Ne.symm hFG⟩, subset_closure hy⟩
  obtain ⟨z, hz, hzB, hzA⟩ := hS Bᶜ Aᶜ hB.isOpen_compl hA.isOpen_compl hSA
    ⟨x, hxS, fun hb => hAB x hxS ⟨hxA, hb⟩⟩
    ⟨y, hyS, fun ha => hAB y hyS ⟨ha, hyB⟩⟩
  obtain ⟨H, hH⟩ := hcover z
  by_cases hH' : label H = label F
  · exact hzA (mem_iUnion.mpr ⟨⟨H, hH'⟩, hH⟩)
  · exact hzB (mem_iUnion.mpr ⟨⟨H, hH'⟩, hH⟩)

/-- Local straightening of every edge interior implies connectivity of the chart dual. -/
theorem chartDualGraph_preconnected_of_straightenable_subarcs
    (D : Drawing J) (charts : ∀ e, EdgeChart D e)
    (hstraight : ∀ (e : E) (t : ArcParameter), 0 < t.val → t.val < 1 →
      ∃ (h : Plane ≃ₜ Plane) (δ : ℝ), 0 < δ ∧
        ∀ s : ArcParameter, |s.val - t.val| < δ → h (D.curve e s) = (s.val, 0)) :
    (chartDualGraph D charts).Preconnected := by
  have hcharts : ∀ (e : E) (t : ArcParameter), 0 < t.val → t.val < 1 →
      ∃ (h : Plane ≃ₜ Plane) (r : ℝ), 0 < r ∧
        (∀ z ∈ LatticeProb.PlaneTopology.axisBox t.val r,
          h.symm z ∈ drawingTrace D ↔ z.2 = 0) ∧
        (∀ s : ArcParameter, |s.val - t.val| < r → h (D.curve e s) = (s.val, 0)) := by
    intro e t ht0 ht1
    obtain ⟨h, δ, hδ, hs⟩ := hstraight e t ht0 ht1
    obtain ⟨r, hr, htrace, hparam⟩ :=
      exists_trace_box_of_straightened_subarc D e t ht0 ht1 h δ hδ hs
    exact ⟨h, r, hr, htrace, hparam⟩
  apply chartDualGraph_preconnected_of_interior_incidence D charts
  intro F e t ht0 ht1 ht
  let m : ArcParameter := ⟨1 / 2, by constructor <;> norm_num⟩
  have hm : D.curve e m ∈ closure (faceRegion D F) :=
    (closure_incidence_of_local_charts D e F (hcharts e) t m ht0 ht1
      (by norm_num [m]) (by norm_num [m])).mp ht
  exact (mem_closure_faceRegion_iff_chart_face D e (charts e) F m
    (by simpa [m] using (charts e).radius_pos)).mp hm

end
end FiniteAvalanches.Electrical.StatementGeometry
