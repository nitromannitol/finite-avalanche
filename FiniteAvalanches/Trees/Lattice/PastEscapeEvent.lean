import FiniteAvalanches.Trees.Lattice.PastMeasurability

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Lattice.PastTail
open LatticeProb SimpleGraph MeasureTheory FiniteAvalanches.Trees.Lattice
open scoped Classical
noncomputable section

private instance latticeWalk_countable (x y : Site 2) : Countable ((lattice 2).Walk x y) :=
  SimpleGraph.Walk.support_injective.countable

/-- The source's closed sup-norm square, for a real radius. -/
def supBall (v : Site 2) (m : ℝ) : Set (Site 2) :=
  {z | ∀ i : Fin 2, |((z i - v i : ℤ) : ℝ)| ≤ m}

/-- Escape of the actual finite outgoing-edge past on the true one-ended tree domain. -/
def pastEscapesSup (v : Site 2) (m : ℝ) : Set EdgeField :=
  {ω | ∃ hT : IsTree ω, ∃ hOne : OneEnded ω,
    ∃ z ∈ vertexPast ω hT hOne v, z ∉ supBall v m}

theorem mem_pastEscapesSup_iff (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (v : Site 2) (m : ℝ) :
    ω ∈ pastEscapesSup v m ↔ ¬vertexPast ω hT hOne v ⊆ supBall v m := by
  simp only [pastEscapesSup, Set.mem_setOf_eq, Set.not_subset]
  constructor
  · rintro ⟨_, _, z, hz, hfar⟩
    exact ⟨z, hz, hfar⟩
  · rintro ⟨z, hz, hfar⟩
    exact ⟨hT, hOne, z, hz, hfar⟩

private theorem cutReachable_iff_walk (ω : EdgeField) (e : LatticeEdge) (x y : Site 2) :
    (cutGraph ω e).Reachable x y ↔ ∃ p : (lattice 2).Walk x y,
      e.val ∉ p.edges ∧ ∀ f ∈ p.edges, f ∈ (toGraph ω).edgeSet := by
  have hle : cutGraph ω e ≤ toGraph ω := SimpleGraph.deleteEdges_le {e.val}
  constructor
  · rintro ⟨p⟩
    refine ⟨p.mapLe (le_trans (hle) (toGraph_le_lattice ω)), ?_, ?_⟩
    · intro he
      have he' : e.val ∈ p.edges := by simpa only [Walk.edges_mapLe_eq_edges] using he
      have hedge := p.edges_subset_edgeSet he'
      rw [cutGraph, SimpleGraph.edgeSet_deleteEdges] at hedge
      exact hedge.2 (by simp)
    · intro f hf
      have hf' : f ∈ p.edges := by simpa only [Walk.edges_mapLe_eq_edges] using hf
      exact SimpleGraph.edgeSet_mono (hle) (p.edges_subset_edgeSet hf')
  · rintro ⟨p, hno, hsel⟩
    apply Nonempty.intro (p.transfer (cutGraph ω e) ?_)
    intro f hf
    rw [cutGraph, SimpleGraph.edgeSet_deleteEdges]
    refine ⟨hsel f hf, ?_⟩
    intro hfe
    have heq : f = e.val := Set.mem_singleton_iff.mp hfe
    exact hno (heq ▸ hf)

private theorem measurableSet_walk_selected {x y : Site 2} (p : (lattice 2).Walk x y) :
    MeasurableSet {ω : EdgeField | ∀ f ∈ p.edges, f ∈ (toGraph ω).edgeSet} := by
  have hE : {ω : EdgeField | ∀ f ∈ p.edges, f ∈ (toGraph ω).edgeSet} =
      {ω | ∀ f (hf : f ∈ p.edges), ω ⟨f, p.edges_subset_edgeSet hf⟩ = true} := by
    ext ω
    exact forall_congr' fun f => forall_congr' fun hf =>
      edge_mem_toGraph_iff ω ⟨f, p.edges_subset_edgeSet hf⟩
  rw [hE]
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun f => MeasurableSet.iInter fun hf =>
    (measurableSet_singleton true).preimage (measurable_pi_apply _)

theorem measurableSet_cutReachable (e : LatticeEdge) (x y : Site 2) :
    MeasurableSet {ω : EdgeField | (cutGraph ω e).Reachable x y} := by
  simp_rw [cutReachable_iff_walk, Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro p
  exact (MeasurableSet.const (e.val ∉ p.edges)).inter (measurableSet_walk_selected p)

private theorem cutComponent_infinite_iff (ω : EdgeField) (e : LatticeEdge) (x : Site 2) :
    (cutComponent ω e x).Infinite ↔ ∀ F : Finset (Site 2),
      ∃ z : Site 2, z ∉ F ∧ (cutGraph ω e).Reachable z x := by
  constructor
  · intro hinf F
    obtain ⟨z, hz, hout⟩ := hinf.exists_notMem_finite F.finite_toSet
    exact ⟨z, hout, (mem_cutComponent_iff ω e x z).mp hz⟩
  · intro h
    by_contra hnot
    have hfin : (cutComponent ω e x).Finite := not_not.mp hnot
    obtain ⟨z, hout, hz⟩ := h hfin.toFinset
    exact hout (hfin.mem_toFinset.mpr ((mem_cutComponent_iff ω e x z).mpr hz))

theorem measurableSet_cutComponent_infinite (e : LatticeEdge) (x : Site 2) :
    MeasurableSet {ω : EdgeField | (cutComponent ω e x).Infinite} := by
  simp_rw [cutComponent_infinite_iff, Set.setOf_forall, Set.setOf_exists]
  apply MeasurableSet.iInter
  intro F
  apply MeasurableSet.iUnion
  intro z
  exact (MeasurableSet.const (z ∉ F)).inter (measurableSet_cutReachable e z x)

private theorem pastEscape_iff_cut_search (ω : EdgeField) (v : Site 2) (m : ℝ) :
    ω ∈ pastEscapesSup v m ↔ (IsTree ω ∧ OneEnded ω) ∧
      ∃ y : Site 2, ∃ hAdj : (lattice 2).Adj v y,
        ω ⟨s(v, y), hAdj⟩ = true ∧
        (cutComponent ω ⟨s(v, y), hAdj⟩ y).Infinite ∧
        ∃ z : Site 2, z ∉ supBall v m ∧
          (cutGraph ω ⟨s(v, y), hAdj⟩).Reachable z v := by
  constructor
  · rintro ⟨hT, hOne, z, hz, hfar⟩
    obtain ⟨hadj, hinf⟩ := (towardEnd_characterization ω hT hOne v _).mp rfl
    have hAdj := toGraph_le_lattice ω hadj
    refine ⟨⟨hT, hOne⟩, towardEnd ω hT hOne v, hAdj, ?_, hinf, z, hfar, ?_⟩
    · exact (toGraph_adj_iff ω hAdj).mp hadj
    · rw [vertexPast_eq_cutComponent] at hz
      exact (mem_cutComponent_iff ω _ v z).mp hz
  · rintro ⟨⟨hT, hOne⟩, y, hAdj, hsel, hinf, z, hfar, hz⟩
    have he := (towardEnd_characterization ω hT hOne v y).mpr ⟨⟨hAdj, hsel⟩, hinf⟩
    subst y
    refine ⟨hT, hOne, z, ?_, hfar⟩
    rw [vertexPast_eq_cutComponent]
    exact (mem_cutComponent_iff ω _ v z).mpr hz

theorem measurableSet_pastEscapesSup (v : Site 2) (m : ℝ) :
    MeasurableSet (pastEscapesSup v m) := by
  have hsearch : MeasurableSet {ω : EdgeField | ∃ y : Site 2,
      ∃ hAdj : (lattice 2).Adj v y, ω ⟨s(v, y), hAdj⟩ = true ∧
      (cutComponent ω ⟨s(v, y), hAdj⟩ y).Infinite ∧
      ∃ z : Site 2, z ∉ supBall v m ∧
        (cutGraph ω ⟨s(v, y), hAdj⟩).Reachable z v} := by
    simp only [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro y
    apply MeasurableSet.iUnion
    intro hAdj
    have hsel : MeasurableSet {ω : EdgeField | ω ⟨s(v, y), hAdj⟩ = true} :=
      (measurableSet_singleton true).preimage (measurable_pi_apply _)
    have hfar : MeasurableSet {ω : EdgeField | ∃ z : Site 2,
        z ∉ supBall v m ∧ (cutGraph ω ⟨s(v, y), hAdj⟩).Reachable z v} := by
      simp only [Set.setOf_exists]
      exact MeasurableSet.iUnion fun z =>
        (MeasurableSet.const (z ∉ supBall v m)).inter (measurableSet_cutReachable _ z v)
    exact hsel.inter ((measurableSet_cutComponent_infinite _ y).inter hfar)
  have hE : pastEscapesSup v m = {ω : EdgeField | IsTree ω ∧ OneEnded ω} ∩
      {ω | ∃ y : Site 2, ∃ hAdj : (lattice 2).Adj v y,
        ω ⟨s(v, y), hAdj⟩ = true ∧
        (cutComponent ω ⟨s(v, y), hAdj⟩ y).Infinite ∧
        ∃ z : Site 2, z ∉ supBall v m ∧
          (cutGraph ω ⟨s(v, y), hAdj⟩).Reachable z v} := by
    ext ω
    exact pastEscape_iff_cut_search ω v m
  rw [hE]
  exact measurableSet_tree_oneEnded.inter hsearch

end
end FiniteAvalanches.Trees.Lattice.PastTail
