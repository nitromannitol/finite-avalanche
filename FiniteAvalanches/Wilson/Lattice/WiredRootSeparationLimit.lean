import FiniteAvalanches.Wilson.Lattice.WiredRootSeparation

/-! The Wilson cylinder law does not connect distinct prescribed roots. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

/-- The lattice edges traversed by a finite lattice walk. -/
def walkLatticeEdges {x y : Site 2} (p : (lattice 2).Walk x y) : Finset LatticeEdge :=
  (p.edges.attach.map fun e => (⟨e.val, p.edges_subset_edgeSet e.property⟩ : LatticeEdge)).toFinset

/-- The walk's lattice edge set contains exactly its traversed edges. -/
theorem mem_walkLatticeEdges {x y : Site 2} (p : (lattice 2).Walk x y) (e : LatticeEdge) :
    e ∈ walkLatticeEdges p ↔ e.val ∈ p.edges := by
  simp only [walkLatticeEdges, List.mem_toFinset, List.mem_map, List.mem_attach, true_and]
  constructor
  · rintro ⟨a, rfl⟩
    exact a.property
  · intro he
    exact ⟨⟨e.val, he⟩, Subtype.ext rfl⟩

/-- Selected edge indicators supply a walk in the selected graph. -/
theorem walk_reachable_of_edge_values {x y : Site 2} (p : (lattice 2).Walk x y)
    (f : EdgeField) (h : ∀ e ∈ walkLatticeEdges p, f e = true) :
    (toGraph f).Reachable x y := by
  apply (p.transfer (toGraph f) ?_).reachable
  intro e he
  let e' : LatticeEdge := ⟨e, p.edges_subset_edgeSet he⟩
  exact (edge_mem_toGraph_iff f e').mpr (h e' ((mem_walkLatticeEdges p e').mpr he))

/-- A fixed walk between distinct in-box roots cannot be entirely selected. -/
theorem finiteForest_root_walk_not_selected (R : RootPair) (B : ℕ) (F : FiniteForest R B)
    {r s : Site 2} (hr : r ∈ R.zero ∪ R.one) (hs : s ∈ R.zero ∪ R.one)
    (hbr : FiniteWired.inBox B r) (hbs : FiniteWired.inBox B s) (hne : r ≠ s)
    (p : (lattice 2).Walk r s) :
    ¬(∀ e ∈ walkLatticeEdges p, finiteEdgeField R B F e = true) := by
  intro he
  exact finiteForest_roots_not_reachable R B F hr hs hbr hbs hne
    (walk_reachable_of_edge_values p (finiteEdgeField R B F) he)

/-- Any specified walk between distinct prescribed roots has zero probability
of being entirely selected under the cylinder law. -/
theorem IsWilsonCylinderLaw.root_walk_measure_zero (R : RootPair)
    (ν : ProbabilityMeasure ForestField) (hν : IsWilsonCylinderLaw R ν)
    {r s : Site 2} (hr : r ∈ R.zero ∪ R.one) (hs : s ∈ R.zero ∪ R.one)
    (hne : r ≠ s) (p : (lattice 2).Walk r s) :
    (ν : Measure ForestField)
      (jointEvent (walkLatticeEdges p) ∅ (fun _ => true) (fun _ => false)) = 0 := by
  let E := walkLatticeEdges p
  let pe : LatticeEdge → Bool := fun _ => true
  let pc : Site 2 → Bool := fun _ => false
  obtain ⟨q, n, hE, hD⟩ := exists_finite_queries E ∅
  have ht := finiteForestLaw_jointEvent_tendsto R q (fun _ => 0) (fun _ _ => 0)
    n E ∅ pe pc hE hD
  have hz : ∀ᶠ B : ℕ in atTop, finiteForestLaw R B (jointEvent E ∅ pe pc) = 0 := by
    filter_upwards [eventually_finiteWired_inBox r, eventually_finiteWired_inBox s] with B hbr hbs
    rw [finiteForestLaw_jointEvent]
    have hempty : wiredObservationCylinder R B E ∅ pe pc = ∅ := by
      ext F
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hF
      apply finiteForest_root_walk_not_selected R B F hr hs hbr hbs hne p
      exact hF.1
    rw [hempty, measure_empty]
  have hz' : (fun _ : ℕ => (0 : ℝ≥0∞)) =ᶠ[atTop]
      (fun B => finiteForestLaw R B (jointEvent E ∅ pe pc)) := by
    filter_upwards [hz] with B hB
    exact hB.symm
  have hlim : Tendsto (fun B : ℕ => finiteForestLaw R B (jointEvent E ∅ pe pc)) atTop
      (nhds 0) := tendsto_const_nhds.congr' hz'
  have hsamp := tendsto_nhds_unique ht hlim
  exact (hν q n E ∅ pe pc hE hD).trans hsamp


private instance latticeWalk_countable (x y : Site 2) :
    Countable ((lattice 2).Walk x y) :=
  SimpleGraph.Walk.support_injective.countable

/-- Distinct prescribed roots are almost surely in different components. -/
theorem IsWilsonCylinderLaw.ae_roots_separated (R : RootPair)
    (ν : ProbabilityMeasure ForestField) (hν : IsWilsonCylinderLaw R ν) :
    ∀ᵐ ω ∂(ν : Measure ForestField), ∀ r s, r ∈ R.zero ∪ R.one →
      s ∈ R.zero ∪ R.one → (toGraph ω.1).Reachable r s → r = s := by
  apply ae_all_iff.mpr
  intro r
  apply ae_all_iff.mpr
  intro s
  by_cases hr : r ∈ R.zero ∪ R.one
  · by_cases hs : s ∈ R.zero ∪ R.one
    · by_cases hne : r ≠ s
      · have hall : ∀ᵐ ω ∂(ν : Measure ForestField),
            ∀ p : (lattice 2).Walk r s,
              ω ∉ jointEvent (walkLatticeEdges p) ∅ (fun _ => true) (fun _ => false) := by
          apply ae_all_iff.mpr
          intro p
          exact (measure_eq_zero_iff_ae_notMem).mp
            (hν.root_walk_measure_zero R ν hr hs hne p)
        filter_upwards [hall] with ω hω _ _ hreach
        obtain ⟨p⟩ := hreach
        let q := p.mapLe (toGraph_le_lattice ω.1)
        have he : ∀ e ∈ walkLatticeEdges q, ω.1 e = true := by
          intro e he
          have hm : e.val ∈ p.edges := by
            have hq := (mem_walkLatticeEdges q e).mp he
            simpa only [q, SimpleGraph.Walk.edges_mapLe_eq_edges] using hq
          exact (edge_mem_toGraph_iff ω.1 e).mp (p.edges_subset_edgeSet hm)
        exact (hω q ⟨he, by simp⟩).elim
      · exact Filter.Eventually.of_forall fun _ _ _ _ => not_ne_iff.mp hne
    · exact Filter.Eventually.of_forall fun _ _ hs' _ => (hs hs').elim
  · exact Filter.Eventually.of_forall fun _ hr' => (hr hr').elim

end
end FiniteAvalanches.Wilson.Lattice
