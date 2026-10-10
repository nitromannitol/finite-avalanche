import FiniteAvalanches.Trees.Lattice.SourceObjects
import FiniteAvalanches.Trees.Lattice.EuclideanPaths

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Lattice.PastTail
open LatticeProb SimpleGraph MeasureTheory FiniteAvalanches.Trees.Lattice
open scoped Classical
noncomputable section

private instance latticeWalk_countable (x y : Site 2) : Countable ((lattice 2).Walk x y) :=
  SimpleGraph.Walk.support_injective.countable

/-- Actual reachability while avoiding the specified finite vertex set. -/
def avoidingReachable (ω : EdgeField) (K : Finset (Site 2)) (x y : Site 2) : Prop :=
  ∃ hx : x ∉ (K : Set (Site 2)), ∃ hy : y ∉ (K : Set (Site 2)),
    ((toGraph ω).induce (K : Set (Site 2))ᶜ).Reachable ⟨x, hx⟩ ⟨y, hy⟩

private theorem avoidingReachable_iff_walk (ω : EdgeField) (K : Finset (Site 2))
    (x y : Site 2) : avoidingReachable ω K x y ↔
    ∃ p : (lattice 2).Walk x y,
      (∀ z ∈ p.support, z ∉ (K : Set (Site 2))) ∧
      (∀ e ∈ p.edges, e ∈ (toGraph ω).edgeSet) := by
  constructor
  · rintro ⟨hx, hy, ⟨p⟩⟩
    let f : (toGraph ω).induce (K : Set (Site 2))ᶜ →g toGraph ω := ⟨Subtype.val, fun h => h⟩
    let q := (p.map f).copy rfl rfl
    refine ⟨q.mapLe (toGraph_le_lattice ω), ?_, ?_⟩
    · intro z hz
      have hz' : z ∈ (p.map f).support := by
        simpa only [SimpleGraph.Walk.support_mapLe_eq_support, q, SimpleGraph.Walk.support_copy] using hz
      rw [SimpleGraph.Walk.support_map] at hz'
      obtain ⟨a, _, ha⟩ := List.mem_map.mp hz'
      exact ha ▸ a.property
    · intro e he
      exact q.edges_subset_edgeSet
        (by simpa only [SimpleGraph.Walk.edges_mapLe_eq_edges] using he)
  · rintro ⟨p, havoid, hsel⟩
    have hx := havoid x p.start_mem_support
    have hy := havoid y p.end_mem_support
    refine ⟨hx, hy, ?_⟩
    let q := p.transfer (toGraph ω) hsel
    have hq : ∀ z ∈ q.support, z ∈ (K : Set (Site 2))ᶜ := by
      simpa only [q, SimpleGraph.Walk.support_transfer, Set.mem_compl_iff] using havoid
    exact ((q.induce (K : Set (Site 2))ᶜ hq).copy (Subtype.ext rfl) (Subtype.ext rfl)).reachable

private theorem measurableSet_walk_selected {x y : Site 2} (p : (lattice 2).Walk x y) :
    MeasurableSet {ω : EdgeField | ∀ e ∈ p.edges, e ∈ (toGraph ω).edgeSet} := by
  have hE : {ω : EdgeField | ∀ e ∈ p.edges, e ∈ (toGraph ω).edgeSet} =
      {ω | ∀ e (he : e ∈ p.edges), ω ⟨e, p.edges_subset_edgeSet he⟩ = true} := by
    ext ω
    exact forall_congr' fun e => forall_congr' fun he =>
      edge_mem_toGraph_iff ω ⟨e, p.edges_subset_edgeSet he⟩
  rw [hE]
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun e => MeasurableSet.iInter fun he =>
    (measurableSet_singleton true).preimage (measurable_pi_apply _)

theorem measurableSet_avoidingReachable (K : Finset (Site 2)) (x y : Site 2) :
    MeasurableSet {ω : EdgeField | avoidingReachable ω K x y} := by
  simp_rw [avoidingReachable_iff_walk, Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro p
  have hc : MeasurableSet {ω : EdgeField | ∀ z ∈ p.support, z ∉ (K : Set (Site 2))} :=
    MeasurableSet.const _
  exact hc.inter (measurableSet_walk_selected p)

/-- In a locally finite lattice tree, one end is equivalent to finite-complement
components coalescing outside a sufficiently large finite vertex set. -/
theorem oneEnded_iff_finite_confinement (ω : EdgeField) (hT : IsTree ω) :
    OneEnded ω ↔ ∀ K : Finset (Site 2), ∃ F : Finset (Site 2),
      ∀ x y : Site 2, x ∉ F → y ∉ F → avoidingReachable ω K x y := by
  letI : Fact (toGraph ω).Preconnected := ⟨hT.connected.preconnected⟩
  constructor
  · intro hOne K
    obtain ⟨C, hCinf, hUnique⟩ := unique_infinite_components_of_oneEnded ω hT hOne K
    have hother : ∀ D : (toGraph ω).ComponentCompl (K : Set (Site 2)),
        D ≠ C → D.supp.Finite := by
      intro D hne
      by_contra hDinf
      exact hne (hUnique D hDinf)
    have hfin : (⋃ D : {D : (toGraph ω).ComponentCompl (K : Set (Site 2)) // D ≠ C},
        D.val.supp).Finite := Set.finite_iUnion fun D => hother D.val D.property
    have hcompl : C.suppᶜ.Finite := by
      apply (K.finite_toSet.union hfin).subset
      intro x hx
      by_cases hxK : x ∈ (K : Set (Site 2))
      · exact Or.inl hxK
      · exact Or.inr (Set.mem_iUnion.mpr
          ⟨⟨(toGraph ω).componentComplMk hxK,
            fun he => hx (he ▸ (toGraph ω).componentComplMk_mem hxK)⟩,
            (toGraph ω).componentComplMk_mem hxK⟩)
    refine ⟨hcompl.toFinset, ?_⟩
    intro x y hx hy
    have hxC : x ∈ C.supp := by simpa only [hcompl.mem_toFinset, Set.mem_compl_iff, not_not] using hx
    have hyC : y ∈ C.supp := by simpa only [hcompl.mem_toFinset, Set.mem_compl_iff, not_not] using hy
    obtain ⟨hxK, hxcomp⟩ := hxC
    obtain ⟨hyK, hycomp⟩ := hyC
    exact ⟨hxK, hyK, SimpleGraph.ConnectedComponent.exact (hxcomp.trans hycomp.symm)⟩
  · intro hconf
    apply oneEnded_of_unique_infinite_components ω hT
    intro K
    obtain ⟨e⟩ := Set.nonempty_coe_sort.mpr (SimpleGraph.nonempty_ends_of_infinite (toGraph ω))
    let C := e.val (Opposite.op K)
    have hCinf : C.supp.Infinite := SimpleGraph.end_componentCompl_infinite _ e _
    refine ⟨C, hCinf, ?_⟩
    intro D hDinf
    obtain ⟨F, hF⟩ := hconf K
    obtain ⟨x, hxD, hxF⟩ := hDinf.exists_notMem_finite F.finite_toSet
    obtain ⟨y, hyC, hyF⟩ := hCinf.exists_notMem_finite F.finite_toSet
    obtain ⟨hxK, hxcomp⟩ := hxD
    obtain ⟨hyK, hycomp⟩ := hyC
    obtain ⟨_, _, hreach⟩ := hF x y hxF hyF
    exact hxcomp.symm.trans ((SimpleGraph.ConnectedComponent.sound hreach).trans hycomp)

theorem measurableSet_tree_oneEnded :
    MeasurableSet {ω : EdgeField | IsTree ω ∧ OneEnded ω} := by
  have hconf : MeasurableSet {ω : EdgeField | ∀ K : Finset (Site 2),
      ∃ F : Finset (Site 2), ∀ x y : Site 2,
        x ∉ F → y ∉ F → avoidingReachable ω K x y} := by
    simp only [Set.setOf_forall, Set.setOf_exists]
    apply MeasurableSet.iInter
    intro K
    apply MeasurableSet.iUnion
    intro F
    apply MeasurableSet.iInter
    intro x
    apply MeasurableSet.iInter
    intro y
    exact MeasurableSet.iInter fun _hx => MeasurableSet.iInter fun _hy =>
      measurableSet_avoidingReachable K x y
  have hE : {ω : EdgeField | IsTree ω ∧ OneEnded ω} =
      {ω : EdgeField | IsTree ω} ∩ {ω | ∀ K : Finset (Site 2),
        ∃ F : Finset (Site 2), ∀ x y : Site 2,
          x ∉ F → y ∉ F → avoidingReachable ω K x y} := by
    ext ω
    constructor
    · rintro ⟨hT, hOne⟩
      exact ⟨hT, (oneEnded_iff_finite_confinement ω hT).mp hOne⟩
    · rintro ⟨hT, hconf⟩
      exact ⟨hT, (oneEnded_iff_finite_confinement ω hT).mpr hconf⟩
  rw [hE]
  exact BarlowMasson.measurableSet_isTree.inter hconf

end
end FiniteAvalanches.Trees.Lattice.PastTail
