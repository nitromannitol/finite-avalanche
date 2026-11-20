import FiniteAvalanches.Wilson.Lattice.WiredFiniteAcyclic

/-! Acyclicity of the limiting Wilson cylinder law. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

/-- A cylinder excluded from every finite wired forest has zero limiting mass. -/
theorem IsWilsonCylinderLaw.jointEvent_measure_zero_of_finite (R : RootPair)
    (ν : ProbabilityMeasure ForestField) (hν : IsWilsonCylinderLaw R ν)
    (E : Finset LatticeEdge) (D : Finset (Site 2))
    (pe : LatticeEdge → Bool) (pc : Site 2 → Bool)
    (h : ∀ B : ℕ, wiredObservationCylinder R B E D pe pc = ∅) :
    (ν : Measure ForestField) (jointEvent E D pe pc) = 0 := by
  obtain ⟨q, n, hE, hD⟩ := exists_finite_queries E D
  have ht := finiteForestLaw_jointEvent_tendsto R q (fun _ => 0) (fun _ _ => 0)
    n E D pe pc hE hD
  have hz : (fun B : ℕ => finiteForestLaw R B (jointEvent E D pe pc)) = fun _ => 0 := by
    funext B
    rw [finiteForestLaw_jointEvent, h B, measure_empty]
  rw [hz] at ht
  have he := tendsto_nhds_unique ht tendsto_const_nhds
  exact (hν q n E D pe pc hE hD).trans he

/-- A fixed lattice cycle is absent from every finite wired forest. -/
theorem finiteForest_cycle_not_selected (R : RootPair) (B : ℕ) (F : FiniteForest R B)
    {x : Site 2} (p : (lattice 2).Walk x x) (hp : p.IsCycle) :
    ¬(∀ e ∈ walkLatticeEdges p, finiteEdgeField R B F e = true) := by
  intro he
  have hedges : ∀ e ∈ p.edges, e ∈ (toGraph (finiteEdgeField R B F)).edgeSet := by
    intro e he'
    let e' : LatticeEdge := ⟨e, p.edges_subset_edgeSet he'⟩
    exact (edge_mem_toGraph_iff _ e').mpr (he e' ((mem_walkLatticeEdges p e').mpr he'))
  exact finiteEdgeField_isAcyclic R B F (p.transfer _ hedges) (hp.transfer hedges)

/-- A fixed lattice cycle has zero probability of being entirely selected. -/
theorem IsWilsonCylinderLaw.cycle_measure_zero (R : RootPair)
    (ν : ProbabilityMeasure ForestField) (hν : IsWilsonCylinderLaw R ν)
    {x : Site 2} (p : (lattice 2).Walk x x) (hp : p.IsCycle) :
    (ν : Measure ForestField)
      (jointEvent (walkLatticeEdges p) ∅ (fun _ => true) (fun _ => false)) = 0 := by
  apply hν.jointEvent_measure_zero_of_finite R ν
  intro B
  ext F
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hF
  exact finiteForest_cycle_not_selected R B F p hp hF.1

private instance latticeWalk_countable (x y : Site 2) :
    Countable ((lattice 2).Walk x y) :=
  SimpleGraph.Walk.support_injective.countable

/-- The selected lattice graph is almost surely acyclic. -/
theorem IsWilsonCylinderLaw.ae_acyclic (R : RootPair)
    (ν : ProbabilityMeasure ForestField) (hν : IsWilsonCylinderLaw R ν) :
    ∀ᵐ ω ∂(ν : Measure ForestField), (toGraph ω.1).IsAcyclic := by
  have hall : ∀ᵐ ω ∂(ν : Measure ForestField), ∀ x : Site 2,
      ∀ p : (lattice 2).Walk x x, p.IsCycle →
        ω ∉ jointEvent (walkLatticeEdges p) ∅ (fun _ => true) (fun _ => false) := by
    apply ae_all_iff.mpr
    intro x
    apply ae_all_iff.mpr
    intro p
    by_cases hp : p.IsCycle
    · filter_upwards [(measure_eq_zero_iff_ae_notMem).mp
        (hν.cycle_measure_zero R ν p hp)] with ω hω _
      exact hω
    · exact Filter.Eventually.of_forall fun _ hp' => (hp hp').elim
  filter_upwards [hall] with ω hω
  intro x p hp
  let q := p.mapLe (toGraph_le_lattice ω.1)
  have hq : q.IsCycle := hp.mapLe (toGraph_le_lattice ω.1)
  apply hω x q hq
  constructor
  · intro e he
    have hm : e.val ∈ p.edges := by
      have hmem := (mem_walkLatticeEdges q e).mp he
      simpa only [q, SimpleGraph.Walk.edges_mapLe_eq_edges] using hmem
    exact (edge_mem_toGraph_iff ω.1 e).mp (p.edges_subset_edgeSet hm)
  · simp

end
end FiniteAvalanches.Wilson.Lattice
