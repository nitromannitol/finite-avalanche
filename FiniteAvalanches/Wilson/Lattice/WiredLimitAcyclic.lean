import FiniteAvalanches.Wilson.Lattice.FiniteUstWeakLimit
import FiniteAvalanches.Wilson.Lattice.WiredAcyclicLimit

/-! Acyclicity of every weak wired spanning tree limit. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

/-- A fixed lattice cycle has zero mass under every weak wired UST limit. -/
theorem wiredLimit_cycle_measure_zero (ν : ProbabilityMeasure EdgeField)
    (hν : Tendsto finiteProbability atTop (nhds ν)) {x : Site 2}
    (p : (lattice 2).Walk x x) (hp : p.IsCycle) :
    (ν : Measure EdgeField) (FiniteAvalanches.Trees.Lattice.cylinder (walkLatticeEdges p) (fun _ => true)) = 0 := by
  let E := walkLatticeEdges p
  obtain ⟨q, n, hE, _⟩ := exists_finite_queries E ∅
  have hf := distantOrigin_finiteForestLaw_edge_tendsto q (fun _ => 0) (fun _ _ => 0)
    n E (fun _ => true) hE
  have hz : (fun B => finiteForestLaw (distantOriginRootPair B) B
      (jointEvent E ∅ (fun _ => true) (fun _ => false))) = fun _ => 0 := by
    funext B
    rw [finiteForestLaw_jointEvent]
    have he : wiredObservationCylinder (distantOriginRootPair B) B E ∅
        (fun _ => true) (fun _ => false) = ∅ := by
      ext F
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hF
      exact finiteForest_cycle_not_selected (distantOriginRootPair B) B F p hp hF.1
    rw [he, measure_empty]
  rw [hz] at hf
  have hsample : wilsonRows (originSamplerEvent ((List.range n).map q) E (fun _ => true)) = 0 :=
    tendsto_nhds_unique hf tendsto_const_nhds
  have hfinite := finiteLaw_cylinder_tendsto_originSampler q (fun _ => 0) (fun _ _ => 0)
    (fun _ => rfl) n E (fun _ => true) hE
  have hcluster := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hν (E := FiniteAvalanches.Trees.Lattice.cylinder E (fun _ => true)) (by
      rw [(isClopen_cylinder E (fun _ => true)).frontier_eq]
      exact measure_empty)
  have heq := tendsto_nhds_unique hcluster hfinite
  have hevent : originSamplerEvent ((List.range n).map q) E
      (fun e => if h : e ∈ E then (fun _ : E => true) ⟨e, h⟩ else false) =
      originSamplerEvent ((List.range n).map q) E (fun _ => true) := by
    ext rows
    simp only [originSamplerEvent, Set.mem_setOf_eq]
    constructor <;> rintro ⟨out, hout, he⟩ <;> refine ⟨out, hout, ?_⟩ <;> intro e heE
    · simpa only [dif_pos heE] using he e heE
    · simpa only [dif_pos heE] using he e heE
  rw [hevent, hsample] at heq
  exact heq

private instance latticeWalk_countable (x y : Site 2) : Countable ((lattice 2).Walk x y) :=
  SimpleGraph.Walk.support_injective.countable

/-- Every weak wired UST limit is almost surely an acyclic lattice subgraph. -/
theorem wiredLimit_ae_acyclic (ν : ProbabilityMeasure EdgeField)
    (hν : Tendsto finiteProbability atTop (nhds ν)) :
    ∀ᵐ ω ∂(ν : Measure EdgeField), (toGraph ω).IsAcyclic := by
  have hall : ∀ᵐ ω ∂(ν : Measure EdgeField), ∀ x : Site 2,
      ∀ p : (lattice 2).Walk x x, p.IsCycle →
        ω ∉ FiniteAvalanches.Trees.Lattice.cylinder (walkLatticeEdges p) (fun _ => true) := by
    apply ae_all_iff.mpr
    intro x
    apply ae_all_iff.mpr
    intro p
    by_cases hp : p.IsCycle
    · filter_upwards [(measure_eq_zero_iff_ae_notMem).mp
        (wiredLimit_cycle_measure_zero ν hν p hp)] with ω hω _
      exact hω
    · exact Filter.Eventually.of_forall fun _ hp' => (hp hp').elim
  filter_upwards [hall] with ω hω
  intro x p hp
  let q := p.mapLe (toGraph_le_lattice ω)
  have hq : q.IsCycle := hp.mapLe (toGraph_le_lattice ω)
  apply hω x q hq
  change (walkLatticeEdges q).restrict ω = fun _ => true
  funext e
  have hm : e.val.val ∈ p.edges := by
    have hmem := (mem_walkLatticeEdges q e.val).mp e.property
    simpa only [q, SimpleGraph.Walk.edges_mapLe_eq_edges] using hmem
  exact (edge_mem_toGraph_iff ω e.val).mp (p.edges_subset_edgeSet hm)

end
end FiniteAvalanches.Wilson.Lattice
