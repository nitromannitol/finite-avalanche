import FiniteAvalanches.Wilson.Lattice.Paths
import FiniteAvalanches.Trees.RootedPaths
import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false

namespace FiniteAvalanches.Trees.Lattice.BarlowMasson
open LatticeProb MeasureTheory FiniteAvalanches.Trees.Lattice
open scoped Classical
noncomputable section

/-- The literal Euclidean distance between integer lattice sites, not the Pi sup norm. -/
def euclideanDistance (x z : Site 2) : ℝ :=
  Real.sqrt (∑ i : Fin 2, ((z i - x i : ℤ) : ℝ) ^ 2)

/-- The source's closed Euclidean ball, including all sites at distance exactly `r`. -/
def euclideanBall (x : Site 2) (r : ℝ) : Set (Site 2) :=
  {z | euclideanDistance x z ≤ r}

/-- The unique actual finite simple path, selected only on the full tree carrier. -/
def treePath (ω : EdgeField) (hω : IsTree ω) (x y : Site 2) :
    (toGraph ω).Walk x y := FiniteAvalanches.Trees.RootedPaths.path hω x y

theorem treePath_full_characterization (ω : EdgeField) (hω : IsTree ω)
    (x y : Site 2) (p : (toGraph ω).Walk x y) :
    treePath ω hω x y = p ↔ p.IsPath := by
  constructor
  · intro h
    rw [← h]
    exact FiniteAvalanches.Trees.RootedPaths.path_isPath hω x y
  · exact FiniteAvalanches.Trees.RootedPaths.path_eq hω p

theorem treePath_support_finite (ω : EdgeField) (hω : IsTree ω) (x y : Site 2) :
    ((treePath ω hω x y).support.toFinset : Set (Site 2)).Finite :=
  (treePath ω hω x y).support.toFinset.finite_toSet

/-- A selected path leaves the source's Euclidean ball. No path is assigned to a
disconnected or cyclic field; membership includes its actual tree certificate. -/
def treePathLeavesEuclidean (x y : Site 2) (r : ℝ) : Set EdgeField :=
  {ω | ∃ hω : IsTree ω, ∃ z ∈ (treePath ω hω x y).support, z ∉ euclideanBall x r}

theorem mem_treePathLeavesEuclidean_iff (ω : EdgeField) (hω : IsTree ω)
    (x y : Site 2) (r : ℝ) :
    ω ∈ treePathLeavesEuclidean x y r ↔
      ¬((treePath ω hω x y).support.toFinset : Set (Site 2)) ⊆ euclideanBall x r := by
  simp only [treePathLeavesEuclidean, Set.mem_setOf_eq, Set.not_subset,
    Finset.mem_coe, List.mem_toFinset]
  constructor
  · rintro ⟨_, z, hz, hout⟩
    exact ⟨z, hz, hout⟩
  · rintro ⟨z, hz, hout⟩
    exact ⟨hω, z, hz, hout⟩

private instance latticeWalk_countable (x y : Site 2) :
    Countable ((lattice 2).Walk x y) :=
  SimpleGraph.Walk.support_injective.countable

private theorem edge_mem_toGraph_iff (ω : EdgeField) (e : LatticeEdge) :
    e.val ∈ (toGraph ω).edgeSet ↔ ω e = true := by
  rcases e with ⟨e, he⟩
  revert he
  refine Sym2.inductionOn e ?_
  intro x y hxy
  exact (toGraph ω).mem_edgeSet.trans (toGraph_adj_iff ω hxy)

private def walkPresent {x y : Site 2} (p : (lattice 2).Walk x y) (ω : EdgeField) : Prop :=
  ∀ e ∈ p.edges, e ∈ (toGraph ω).edgeSet

private theorem measurableSet_walkPresent {x y : Site 2} (p : (lattice 2).Walk x y) :
    MeasurableSet {ω | walkPresent p ω} := by
  have hE : {ω | walkPresent p ω} =
      {ω | ∀ e (he : e ∈ p.edges), ω ⟨e, p.edges_subset_edgeSet he⟩ = true} := by
    ext ω
    exact forall_congr' fun e => forall_congr' fun he =>
      edge_mem_toGraph_iff ω ⟨e, p.edges_subset_edgeSet he⟩
  rw [hE]
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun e => MeasurableSet.iInter fun he =>
    (measurableSet_singleton true).preimage (measurable_pi_apply _)

private theorem connected_iff_walkPresent (ω : EdgeField) :
    (toGraph ω).Connected ↔ ∀ x y : Site 2, ∃ p : (lattice 2).Walk x y, walkPresent p ω := by
  constructor
  · intro h x y
    obtain ⟨p⟩ := h.preconnected x y
    refine ⟨p.mapLe (toGraph_le_lattice ω), ?_⟩
    intro e he
    exact p.edges_subset_edgeSet
      (by simpa only [SimpleGraph.Walk.edges_mapLe_eq_edges] using he)
  · intro h
    exact SimpleGraph.Connected.mk fun x y => by
      obtain ⟨p, hp⟩ := h x y
      exact (p.transfer (toGraph ω) hp).reachable

private theorem acyclic_iff_walkPresent (ω : EdgeField) :
    (toGraph ω).IsAcyclic ↔ ∀ x : Site 2, ∀ p : (lattice 2).Walk x x,
      p.IsCycle → ¬walkPresent p ω := by
  constructor
  · intro h x p hp hpres
    exact h (p.transfer (toGraph ω) hpres) (hp.transfer hpres)
  · intro h x p hp
    apply h x (p.mapLe (toGraph_le_lattice ω)) (hp.mapLe (toGraph_le_lattice ω))
    intro e he
    exact p.edges_subset_edgeSet
      (by simpa only [SimpleGraph.Walk.edges_mapLe_eq_edges] using he)

theorem measurableSet_isTree : MeasurableSet {ω : EdgeField | IsTree ω} := by
  have hc : MeasurableSet {ω : EdgeField | (toGraph ω).Connected} := by
    simp_rw [connected_iff_walkPresent, Set.setOf_forall, Set.setOf_exists]
    exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun y =>
      MeasurableSet.iUnion fun p => measurableSet_walkPresent p
  have ha : MeasurableSet {ω : EdgeField | (toGraph ω).IsAcyclic} := by
    have hA : {ω : EdgeField | (toGraph ω).IsAcyclic} =
        ⋂ x : Site 2, ⋂ p : (lattice 2).Walk x x, {ω | p.IsCycle → ¬walkPresent p ω} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact acyclic_iff_walkPresent ω
    rw [hA]
    apply MeasurableSet.iInter
    intro x
    apply MeasurableSet.iInter
    intro p
    by_cases hp : p.IsCycle
    · have hE : {ω | p.IsCycle → ¬walkPresent p ω} = {ω | walkPresent p ω}ᶜ := by
        ext ω
        simp only [hp, true_implies, Set.mem_setOf_eq, Set.mem_compl_iff]
      rw [hE]
      exact (measurableSet_walkPresent p).compl
    · simp only [hp, false_implies, Set.setOf_true]
      exact MeasurableSet.univ
  have he : {ω : EdgeField | IsTree ω} =
      {ω | (toGraph ω).Connected} ∩ {ω | (toGraph ω).IsAcyclic} := by
    ext ω
    exact SimpleGraph.isTree_iff (toGraph ω)
  rw [he]
  exact hc.inter ha

private theorem leaves_iff_lattice_path (ω : EdgeField) (x y : Site 2) (r : ℝ) :
    ω ∈ treePathLeavesEuclidean x y r ↔ IsTree ω ∧
      ∃ p : (lattice 2).Walk x y, p.IsPath ∧ walkPresent p ω ∧
        ∃ z ∈ p.support, z ∉ euclideanBall x r := by
  constructor
  · rintro ⟨hω, z, hz, hout⟩
    let p := treePath ω hω x y
    refine ⟨hω, p.mapLe (toGraph_le_lattice ω),
      (FiniteAvalanches.Trees.RootedPaths.path_isPath hω x y).mapLe _, ?_, ?_⟩
    · intro e he
      exact p.edges_subset_edgeSet
        (by simpa only [SimpleGraph.Walk.edges_mapLe_eq_edges] using he)
    · exact ⟨z, by simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hz, hout⟩
  · rintro ⟨hω, p, hp, hpres, z, hz, hout⟩
    have heq := (treePath_full_characterization ω hω x y
      (p.transfer (toGraph ω) hpres)).mpr (hp.transfer hpres)
    refine ⟨hω, z, ?_, hout⟩
    rw [heq, SimpleGraph.Walk.support_transfer]
    exact hz

theorem measurableSet_treePathLeavesEuclidean (x y : Site 2) (r : ℝ) :
    MeasurableSet (treePathLeavesEuclidean x y r) := by
  have hpaths : MeasurableSet {ω : EdgeField | ∃ p : (lattice 2).Walk x y,
      p.IsPath ∧ walkPresent p ω ∧ ∃ z ∈ p.support, z ∉ euclideanBall x r} := by
    simp only [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro p
    by_cases hp : p.IsPath
    · by_cases hfar : ∃ z ∈ p.support, z ∉ euclideanBall x r
      · simpa only [hp, hfar, true_and, and_true] using measurableSet_walkPresent p
      · simp only [hfar, and_false, Set.setOf_false]
        exact MeasurableSet.empty
    · simp only [hp, false_and, Set.setOf_false]
      exact MeasurableSet.empty
  have hE : treePathLeavesEuclidean x y r = {ω : EdgeField | IsTree ω} ∩
      {ω | ∃ p : (lattice 2).Walk x y,
        p.IsPath ∧ walkPresent p ω ∧ ∃ z ∈ p.support, z ∉ euclideanBall x r} := by
    ext ω
    exact leaves_iff_lattice_path ω x y r
  rw [hE]
  exact measurableSet_isTree.inter hpaths

/-- The selected graph path, in the ordinary finite-walk carrier used by Wilson. -/
def treePathFiniteWalk (ω : EdgeField) (hω : IsTree ω) (x y : Site 2) :
    FiniteAvalanches.Wilson.Lattice.FiniteWalk where
  length := (treePath ω hω x y).length
  vertex := fun i => (treePath ω hω x y).getVert i.val
  adjacent := fun i => toGraph_le_lattice ω
    ((treePath ω hω x y).adj_getVert_succ i.isLt)

theorem treePathFiniteWalk_injective (ω : EdgeField) (hω : IsTree ω) (x y : Site 2) :
    Function.Injective (treePathFiniteWalk ω hω x y).vertex := by
  intro i j hij
  apply Fin.ext
  exact (FiniteAvalanches.Trees.RootedPaths.path_isPath hω x y).getVert_injOn
    (Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ j.isLt) hij

theorem treePathFiniteWalk_vertices (ω : EdgeField) (hω : IsTree ω) (x y : Site 2) :
    (treePathFiniteWalk ω hω x y).vertices =
      ((treePath ω hω x y).support.toFinset : Set (Site 2)) := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact List.mem_toFinset.mpr ((treePath ω hω x y).getVert_mem_support i.val)
  · intro hz
    obtain ⟨i, hi, hle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
      (List.mem_toFinset.mp hz)
    exact ⟨⟨i, Nat.lt_succ_of_le hle⟩, hi⟩

end
end FiniteAvalanches.Trees.Lattice.BarlowMasson
