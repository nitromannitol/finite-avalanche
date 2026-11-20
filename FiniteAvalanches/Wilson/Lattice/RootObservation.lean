import FiniteAvalanches.Wilson.Lattice.SamplerFiniteObservation

/-! Root connection events determined by finitely many lattice edges. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- A finite edge pattern connects a site to an original root if it contains
all edges of some finite lattice walk to that root. -/
def rootConnectionPattern (R : RootPair) (x : Site 2) (E : Finset LatticeEdge) : Set (E → Bool) :=
  {f | ∃ r ∈ R.zero ∪ R.one, ∃ p : (lattice 2).Walk x r,
    ∃ h : walkLatticeEdges p ⊆ E, ∀ e (he : e ∈ walkLatticeEdges p), f ⟨e, h he⟩ = true}

/-- The full selected graph connects the given site to an original root. -/
def rootConnectionEvent (R : RootPair) (x : Site 2) : Set ForestField :=
  {ω | ∃ r ∈ R.zero ∪ R.one, (toGraph ω.1).Reachable x r}

/-- A finite successful certificate also gives a connection in the full field. -/
theorem restrictEdgeField_rootConnection_subset (R : RootPair) (x : Site 2)
    (E : Finset LatticeEdge) :
    restrictEdgeField E ⁻¹' rootConnectionPattern R x E ⊆ rootConnectionEvent R x := by
  intro ω h
  obtain ⟨r, hr, p, hsub, hp⟩ := h
  refine ⟨r, hr, walk_reachable_of_edge_values p ω.1 ?_⟩
  intro e he
  exact hp e he

/-- The root connection event is open, since a finite walk certifies it. -/
theorem isOpen_rootConnectionEvent (R : RootPair) (x : Site 2) :
    IsOpen (rootConnectionEvent R x) := by
  have he : rootConnectionEvent R x = ⋃ r : Site 2, ⋃ hr : r ∈ R.zero ∪ R.one,
      ⋃ p : (lattice 2).Walk x r,
        jointEvent (walkLatticeEdges p) ∅ (fun _ => true) (fun _ => false) := by
    ext ω
    simp only [rootConnectionEvent, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨r, hr, ⟨p⟩⟩
      let q := p.mapLe (toGraph_le_lattice ω.1)
      refine ⟨r, hr, q, ?_, by simp⟩
      intro e he
      have hm : e.val ∈ p.edges := by
        have hq := (mem_walkLatticeEdges q e).mp he
        simpa only [q, SimpleGraph.Walk.edges_mapLe_eq_edges] using hq
      exact (edge_mem_toGraph_iff ω.1 e).mp (p.edges_subset_edgeSet hm)
    · rintro ⟨r, hr, p, h⟩
      exact ⟨r, hr, walk_reachable_of_edge_values p ω.1 h.1⟩
  rw [he]
  exact isOpen_iUnion fun r => isOpen_iUnion fun hr => isOpen_iUnion fun p =>
    (isClopen_jointEvent (walkLatticeEdges p) ∅ (fun _ => true) (fun _ => false)).isOpen

/-- Finite root-connection event masses match the finite sampler. -/
theorem IsWilsonCylinderLaw.rootConnectionPattern_measure (R : RootPair)
    (ν : ProbabilityMeasure ForestField) (hν : IsWilsonCylinderLaw R ν)
    (x : Site 2) (q : ℕ → Site 2) (n : ℕ) (E : Finset LatticeEdge)
    (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, q i = z) :
    (ν : Measure ForestField) (restrictEdgeField E ⁻¹' rootConnectionPattern R x E) =
      wilsonRows (samplerEdgeObservation R ((List.range n).map q) E ⁻¹'
        rootConnectionPattern R x E) := by
  have hm : MeasurableSet (rootConnectionPattern R x E) :=
    (Set.to_countable _).measurableSet
  have h := congrArg (fun μ : Measure (E → Bool) => μ (rootConnectionPattern R x E))
    (hν.map_restrictEdgeField R ν q n E hE)
  simpa only [Measure.map_apply (measurable_restrictEdgeField E) hm,
    Measure.map_apply (measurable_samplerEdgeObservation R ((List.range n).map q) E) hm] using h

end
end FiniteAvalanches.Wilson.Lattice
