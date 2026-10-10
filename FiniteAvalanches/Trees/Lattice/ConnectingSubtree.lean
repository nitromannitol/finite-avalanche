import FiniteAvalanches.Trees.Lattice.SourceObjects
import FiniteAvalanches.Trees.RootedPaths
import FiniteAvalanches.Wilson.Lattice.ForestEvents
import FiniteAvalanches.Wilson.Lattice.Law

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Lattice
open LatticeProb SimpleGraph FiniteAvalanches.Wilson.Lattice FiniteAvalanches.Trees
open scoped Classical
noncomputable section

private def selectedRayPrefix (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (x : Site 2) :
    ∀ n, (toGraph ω).Walk x ((orientedRay ω hT hOne x).vertex n)
  | 0 => .nil
  | n + 1 => ((selectedRayPrefix ω hT hOne x n).concat
      ((infiniteRay_isSimpleRay ω hT
        (unique_infinite_components_of_oneEnded ω hT hOne) x).2.2 n)).copy rfl rfl

private theorem selectedRayPrefix_support (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (x : Site 2) (n : ℕ) :
    (selectedRayPrefix ω hT hOne x n).support =
      (List.range (n + 1)).map (orientedRay ω hT hOne x).vertex := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [selectedRayPrefix, Walk.support_copy, Walk.support_concat, ih,
      List.range_succ, List.map_append, List.map_cons, List.map_nil]
    rfl

private theorem truePath_ray_support (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (x : Site 2) (n : ℕ) :
    (RootedPaths.path hT x ((orientedRay ω hT hOne x).vertex n)).support =
      (List.range (n + 1)).map (orientedRay ω hT hOne x).vertex := by
  have hp : (selectedRayPrefix ω hT hOne x n).IsPath := by
    rw [Walk.isPath_def, selectedRayPrefix_support]
    exact List.Nodup.map (orientedRay ω hT hOne x).injective List.nodup_range
  rw [RootedPaths.path_eq hT _ hp, selectedRayPrefix_support]

private theorem mem_truePath_ray (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (x z : Site 2) (n : ℕ) :
    z ∈ (RootedPaths.path hT x ((orientedRay ω hT hOne x).vertex n)).support ↔
      ∃ i ≤ n, (orientedRay ω hT hOne x).vertex i = z := by
  rw [truePath_ray_support]
  simp only [List.mem_map, List.mem_range, Nat.lt_succ_iff]

private theorem ray_add (ω : EdgeField) (hT : IsTree ω) (hOne : OneEnded ω)
    (x : Site 2) (m n : ℕ) :
    (orientedRay ω hT hOne x).vertex (m + n) =
      (orientedRay ω hT hOne ((orientedRay ω hT hOne x).vertex m)).vertex n :=
  infiniteRay_add ω hT (unique_infinite_components_of_oneEnded ω hT hOne) x m n

private theorem earliest_is_rooted_common_ancestor (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (S : Finset (Site 2)) (hS : S.Nonempty) :
    RootedPaths.is_common_ancestor hT (earliestCommonAncestor ω hT hOne S hS)
      (S : Set (Site 2)) (earliestCommonAncestor ω hT hOne S hS) := by
  let c := earliestCommonAncestor ω hT hOne S hS
  have hc := (earliestCommonAncestor_characterization ω hT hOne S hS c).mp rfl
  refine ⟨fun x _ => RootedPaths.ancestor_root hT c x, ?_⟩
  intro b hb
  have hbcommon : ∀ x ∈ S, b ∈ (orientedRay ω hT hOne x).vertices := by
    intro x hx
    obtain ⟨n, hn⟩ := hc.1 x hx
    have hbx := hb x hx
    unfold RootedPaths.ancestor at hbx
    rw [RootedPaths.path_reverse hT c x, Walk.support_reverse] at hbx
    have hbx' := List.mem_reverse.mp hbx
    have hbx'' : b ∈ (RootedPaths.path hT x ((orientedRay ω hT hOne x).vertex n)).support := by
      exact (congrArg (fun v : Site 2 => (RootedPaths.path hT x v).support) hn).symm ▸ hbx'
    obtain ⟨i, _, hi⟩ := (mem_truePath_ray ω hT hOne x b n).mp hbx''
    exact ⟨i, hi⟩
  obtain ⟨x, hx⟩ := hS
  obtain ⟨n, hn⟩ := hc.1 x hx
  obtain ⟨j, hj⟩ := hc.2 b hbcommon
  have hbx := hb x hx
  unfold RootedPaths.ancestor at hbx
  rw [RootedPaths.path_reverse hT c x, Walk.support_reverse] at hbx
  have hbx' := List.mem_reverse.mp hbx
  have hbx'' : b ∈ (RootedPaths.path hT x ((orientedRay ω hT hOne x).vertex n)).support := by
    exact (congrArg (fun v : Site 2 => (RootedPaths.path hT x v).support) hn).symm ▸ hbx'
  obtain ⟨i, hi, hib⟩ := (mem_truePath_ray ω hT hOne x b n).mp hbx''
  have heq : (orientedRay ω hT hOne x).vertex (n + j) =
      (orientedRay ω hT hOne x).vertex i := by
    rw [ray_add, hn, hj, hib]
  have he := (orientedRay ω hT hOne x).injective heq
  have hj0 : j = 0 := by omega
  have hbc : b = c := by
    have hj' : (orientedRay ω hT hOne c).vertex 0 = b := hj0 ▸ hj
    exact hj'.symm
  change RootedPaths.ancestor hT c b c
  rw [hbc]
  exact RootedPaths.ancestor_refl hT c c

/-- The finite union of the true selected-tree paths from the sources to their
first common ancestor. This is not the ancestor's finite past. -/
def connectingSites (ω : EdgeField) (hT : IsTree ω) (hOne : OneEnded ω)
    (S : Finset (Site 2)) (hS : S.Nonempty) : Finset (Site 2) :=
  S.biUnion fun x =>
    (RootedPaths.path hT x (earliestCommonAncestor ω hT hOne S hS)).support.toFinset

theorem mem_connectingSites (ω : EdgeField) (hT : IsTree ω) (hOne : OneEnded ω)
    (S : Finset (Site 2)) (hS : S.Nonempty) (z : Site 2) :
    z ∈ connectingSites ω hT hOne S hS ↔ ∃ x ∈ S,
      z ∈ (RootedPaths.path hT x (earliestCommonAncestor ω hT hOne S hS)).support := by
  simp only [connectingSites, Finset.mem_biUnion, List.mem_toFinset]

/-- The ray-based union is exactly the genuine minimal pairwise-path span. -/
theorem connectingSites_eq_span (ω : EdgeField) (hT : IsTree ω) (hOne : OneEnded ω)
    (S : Finset (Site 2)) (hS : S.Nonempty) :
    (connectingSites ω hT hOne S hS : Set (Site 2)) = RootedPaths.connectingSubtree hT S := by
  let c := earliestCommonAncestor ω hT hOne S hS
  have hc : c ∈ RootedPaths.connectingSubtree hT (S : Set (Site 2)) :=
    RootedPaths.common_ancestor_mem_connectingSubtree hT hS
      (earliest_is_rooted_common_ancestor ω hT hOne S hS)
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, hzx⟩ := (mem_connectingSites ω hT hOne S hS z).mp hz
    exact RootedPaths.connectingSubtree_convex hT (S : Set (Site 2)) hS x
      (RootedPaths.subset_connectingSubtree hT _ hx) c hc z hzx
  · rintro ⟨x, hx, y, hy, hz⟩
    apply (mem_connectingSites ω hT hOne S hS z).mpr
    rcases RootedPaths.path_subset_union hT x y c hz with hz | hz
    · exact ⟨x, hx, hz⟩
    · refine ⟨y, hy, ?_⟩
      rw [RootedPaths.path_reverse hT y c, Walk.support_reverse]
      exact List.mem_reverse.mpr hz

private theorem connected_path_convex {V : Type*} {T : SimpleGraph V}
    (hT : T.IsTree) (A : Set V) (hA : (T.induce A).Connected) :
    RootedPaths.is_path_convex hT A := by
  intro x hx y hy z hz
  obtain ⟨p, hp⟩ := hA.exists_isPath ⟨x, hx⟩ ⟨y, hy⟩
  let f : T.induce A →g T := (SimpleGraph.Embedding.induce A).toHom
  let q : T.Walk x y := (p.map f).copy rfl rfl
  have hp' : q.IsPath := by
    simpa only [q, Walk.isPath_copy] using
      (Walk.isPath_map_iff_of_injective (p := p) (f := f) Subtype.val_injective).mpr hp
  rw [RootedPaths.path_eq hT q hp'] at hz
  simp only [q, Walk.support_copy, Walk.support_map] at hz
  obtain ⟨v, _, hv⟩ := List.mem_map.mp hz
  exact hv ▸ v.property

/-- Full minimality and uniqueness among actual connected selected-tree vertex
sets. The comparison sets may be infinite. -/
theorem connectingSites_characterization (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (S : Finset (Site 2)) (hS : S.Nonempty) (K : Set (Site 2)) :
    K = (connectingSites ω hT hOne S hS : Set (Site 2)) ↔
      (S : Set (Site 2)) ⊆ K ∧ ((toGraph ω).induce K).Connected ∧
      ∀ A : Set (Site 2), (S : Set (Site 2)) ⊆ A →
        ((toGraph ω).induce A).Connected → K ⊆ A := by
  have he := connectingSites_eq_span ω hT hOne S hS
  have hsub : (S : Set (Site 2)) ⊆ (connectingSites ω hT hOne S hS : Set (Site 2)) := by
    rw [he]; exact RootedPaths.subset_connectingSubtree hT _
  have hconn : ((toGraph ω).induce (connectingSites ω hT hOne S hS : Set (Site 2))).Connected := by
    rw [he]; exact RootedPaths.connectingSubtree_connected hT _ hS
  have hmin : ∀ A : Set (Site 2), (S : Set (Site 2)) ⊆ A →
      ((toGraph ω).induce A).Connected →
      (connectingSites ω hT hOne S hS : Set (Site 2)) ⊆ A := by
    intro A hSA hA
    rw [he]
    exact RootedPaths.connectingSubtree_minimal hT _ A (connected_path_convex hT A hA) hSA
  constructor
  · rintro rfl; exact ⟨hsub, hconn, hmin⟩
  · rintro ⟨hSK, hK, hKM⟩
    exact Set.Subset.antisymm (hKM _ hsub hconn) (hmin K hSK hK)

theorem existsUnique_connectingSites (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (S : Finset (Site 2)) (hS : S.Nonempty) :
    ∃! K : Set (Site 2), (S : Set (Site 2)) ⊆ K ∧ ((toGraph ω).induce K).Connected ∧
      ∀ A : Set (Site 2), (S : Set (Site 2)) ⊆ A →
        ((toGraph ω).induce A).Connected → K ⊆ A :=
  ⟨connectingSites ω hT hOne S hS,
    (connectingSites_characterization ω hT hOne S hS _).mp rfl,
    fun K hK => (connectingSites_characterization ω hT hOne S hS K).mpr hK⟩

theorem connectingSites_isTree (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (S : Finset (Site 2)) (hS : S.Nonempty) :
    ((toGraph ω).induce (connectingSites ω hT hOne S hS : Set (Site 2))).IsTree :=
  ⟨((connectingSites_characterization ω hT hOne S hS _).mp rfl).2.1,
    hT.isAcyclic.induce _⟩

theorem connectingSites_witness_independent (ω : EdgeField) (hT hT' : IsTree ω)
    (hOne hOne' : OneEnded ω) (S : Finset (Site 2)) (hS hS' : S.Nonempty) :
    connectingSites ω hT hOne S hS = connectingSites ω hT' hOne' S hS' := rfl

theorem ancestor_mem_connectingSites (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (S : Finset (Site 2)) (hS : S.Nonempty) :
    earliestCommonAncestor ω hT hOne S hS ∈ connectingSites ω hT hOne S hS := by
  have hSex := hS
  obtain ⟨x, hx⟩ := hSex
  exact (mem_connectingSites ω hT hOne S hS _).mpr
    ⟨x, hx, (RootedPaths.path hT x _).end_mem_support⟩

theorem connectingSites_subset_past (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (S : Finset (Site 2)) (hS : S.Nonempty) :
    (connectingSites ω hT hOne S hS : Set (Site 2)) ⊆
      vertexPast ω hT hOne (earliestCommonAncestor ω hT hOne S hS) := by
  intro z hz
  obtain ⟨x, hx, hzx⟩ := (mem_connectingSites ω hT hOne S hS z).mp hz
  have hc := (earliestCommonAncestor_characterization ω hT hOne S hS _).mp rfl
  obtain ⟨n, hn⟩ := hc.1 x hx
  rw [← hn] at hzx
  obtain ⟨i, hi, hiz⟩ := (mem_truePath_ray ω hT hOne x z n).mp hzx
  apply (vertexPast_characterization ω hT hOne _ z).mpr
  refine ⟨n - i, ?_⟩
  rw [← hiz, ← ray_add, Nat.add_sub_of_le hi, hn]

/-- Only the starting vertex of the outgoing ray lies in its cut-component
past; every later vertex lies on the infinite side. -/
theorem orientedRay_mem_vertexPast_iff (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (x : Site 2) (n : ℕ) :
    (orientedRay ω hT hOne x).vertex n ∈ vertexPast ω hT hOne x ↔ n = 0 := by
  constructor
  · intro hp
    obtain ⟨j, hj⟩ := (vertexPast_characterization ω hT hOne x _).mp hp
    have he : (orientedRay ω hT hOne x).vertex (n + j) =
        (orientedRay ω hT hOne x).vertex 0 := by rw [ray_add]; exact hj
    have hij := (orientedRay ω hT hOne x).injective he
    omega
  · rintro rfl
    exact (vertexPast_characterization ω hT hOne x x).mpr ⟨0, rfl⟩

theorem outgoingRay_mem_connectingSites_iff (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (S : Finset (Site 2)) (hS : S.Nonempty) (n : ℕ) :
    (orientedRay ω hT hOne (earliestCommonAncestor ω hT hOne S hS)).vertex n ∈
      connectingSites ω hT hOne S hS ↔ n = 0 := by
  let c := earliestCommonAncestor ω hT hOne S hS
  constructor
  · intro hn
    have hp := connectingSites_subset_past ω hT hOne S hS hn
    exact (orientedRay_mem_vertexPast_iff ω hT hOne c n).mp hp
  · rintro rfl
    exact ancestor_mem_connectingSites ω hT hOne S hS

/-- The actual source connecting subtree and outgoing ray, in the literal
Wilson carrier. Its zero roots are the subtree, not its past. -/
def sourceConnectingPair (ω : EdgeField) (hT : IsTree ω) (hOne : OneEnded ω)
    (S : Finset (Site 2)) (hS : S.Nonempty) : ConnectingPair where
  sites := connectingSites ω hT hOne S hS
  ray := orientedRay ω hT hOne (earliestCommonAncestor ω hT hOne S hS)
  connected := by
    have hle : (toGraph ω).induce (connectingSites ω hT hOne S hS : Set (Site 2)) ≤
        (lattice 2).induce (connectingSites ω hT hOne S hS : Set (Site 2)) :=
      fun _ _ h => toGraph_le_lattice ω h
    apply SimpleGraph.Connected.mono hle
    exact ((connectingSites_characterization ω hT hOne S hS _).mp rfl).2.1
  ray_mem_iff := outgoingRay_mem_connectingSites_iff ω hT hOne S hS

theorem sourceConnectingPair_characterization (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (S : Finset (Site 2)) (hS : S.Nonempty) (p : ConnectingPair) :
    p = sourceConnectingPair ω hT hOne S hS ↔
      p.sites = connectingSites ω hT hOne S hS ∧
      p.ray = orientedRay ω hT hOne (earliestCommonAncestor ω hT hOne S hS) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rcases p with ⟨K, r, hK, hr⟩
    rintro ⟨hK', hr'⟩
    cases hK'; cases hr'; rfl

/-- The color field in the conditional-law statement: exactly the complement
of the actual outgoing-edge cut component. -/
def sourcePastComplement (ω : EdgeField) (hT : IsTree ω) (hOne : OneEnded ω)
    (S : Finset (Site 2)) (hS : S.Nonempty) : ColorField :=
  fun y => decide (y ∉ vertexPast ω hT hOne (earliestCommonAncestor ω hT hOne S hS))

theorem sourcePastComplement_eq_true_iff (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (S : Finset (Site 2)) (hS : S.Nonempty) (y : Site 2) :
    sourcePastComplement ω hT hOne S hS y = true ↔
      y ∉ cutComponent ω (outgoingEdge ω hT hOne (earliestCommonAncestor ω hT hOne S hS))
        (earliestCommonAncestor ω hT hOne S hS) := by
  simp only [sourcePastComplement, decide_eq_true_eq, vertexPast_eq_cutComponent]

/-- Every original lattice neighbor contributes, whether or not its edge was
selected by the tree. -/
def sourceBoundaryCount (ω : EdgeField) (hT : IsTree ω) (hOne : OneEnded ω)
    (S : Finset (Site 2)) (hS : S.Nonempty) : ℕ :=
  contacts (connectingSites ω hT hOne S hS) (sourcePastComplement ω hT hOne S hS)

theorem sourceBoundaryCount_ge_one (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (S : Finset (Site 2)) (hS : S.Nonempty) :
    1 ≤ sourceBoundaryCount ω hT hOne S hS := by
  apply contacts_ge_one (sourceConnectingPair ω hT hOne S hS)
  change decide (_ ∉ vertexPast ω hT hOne _) = true
  rw [decide_eq_true_eq]
  intro hp
  let c := earliestCommonAncestor ω hT hOne S hS
  exact Nat.one_ne_zero ((orientedRay_mem_vertexPast_iff ω hT hOne c 1).mp hp)

/-- The singleton span has exactly one vertex, even when its past has other
vertices. This exercises the minimality characterization. -/
theorem connectingSites_singleton (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (x : Site 2) :
    connectingSites ω hT hOne {x} (Finset.singleton_nonempty x) = {x} := by
  apply Finset.coe_injective
  simp only [Finset.coe_singleton]
  apply ((connectingSites_characterization ω hT hOne {x}
    (Finset.singleton_nonempty x) ({x} : Set (Site 2))).mpr ?_).symm
  refine ⟨by simp, ?_, fun A hA _ => by simpa only [Finset.coe_singleton] using hA⟩
  letI : Nonempty ({x} : Set (Site 2)) := ⟨⟨x, rfl⟩⟩
  apply SimpleGraph.Connected.mk
  intro u v
  have huv : u = v := Subtype.ext (u.property.trans v.property.symm)
  subst v
  exact SimpleGraph.Reachable.refl _

/-- Two sources give precisely their true selected-tree path, rather than an
arbitrary connecting lattice set or the finite ancestor past. -/
theorem connectingSites_pair (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (x y : Site 2) (hS : ({x, y} : Finset (Site 2)).Nonempty) :
    connectingSites ω hT hOne {x, y} hS = (RootedPaths.path hT x y).support.toFinset := by
  let A : Set (Site 2) := {z | z ∈ (RootedPaths.path hT x y).support}
  have he : A = (connectingSites ω hT hOne {x, y} hS : Set (Site 2)) := by
    apply (connectingSites_characterization ω hT hOne {x, y} hS A).mpr
    refine ⟨?_, (RootedPaths.path hT x y).connected_induce_support, ?_⟩
    · intro z hz
      rcases Finset.mem_insert.mp hz with hz | hz
      · exact hz.symm ▸ (RootedPaths.path hT x y).start_mem_support
      · have hzy : z = y := Finset.mem_singleton.mp hz
        subst z
        exact (RootedPaths.path hT x y).end_mem_support
    · intro B hSB hB z hz
      exact connected_path_convex hT B hB x (hSB (by simp)) y (hSB (by simp)) z hz
  apply Finset.coe_injective
  rw [← he]
  ext z
  simp only [A, Set.mem_setOf_eq, Finset.mem_coe, List.mem_toFinset]

namespace ConnectingConsumer
open MeasureTheory

/-- One common UST tree/end witness gives every finite nonempty source set its
actual minimal finite span, outgoing connecting pair, finite cut past and count. -/
theorem actualUST_connecting_objects :
    ∀ᵐ ω ∂(squareLatticeUST : Measure EdgeField),
      ∃ hT : IsTree ω, ∃ hOne : OneEnded ω,
      ∀ (S : Finset (Site 2)) (hS : S.Nonempty),
        ((sourceConnectingPair ω hT hOne S hS).sites : Set (Site 2)) =
          RootedPaths.connectingSubtree hT S ∧
        (vertexPast ω hT hOne (earliestCommonAncestor ω hT hOne S hS)).Finite ∧
        (connectingSites ω hT hOne S hS : Set (Site 2)) ⊆
          vertexPast ω hT hOne (earliestCommonAncestor ω hT hOne S hS) ∧
        1 ≤ sourceBoundaryCount ω hT hOne S hS := by
  filter_upwards [squareLatticeUST_ae_tree_oneEnded] with ω hω
  refine ⟨hω.1, hω.2, ?_⟩
  intro S hS
  exact ⟨connectingSites_eq_span ω hω.1 hω.2 S hS,
    vertexPast_finite ω hω.1 hω.2 _,
    connectingSites_subset_past ω hω.1 hω.2 S hS,
    sourceBoundaryCount_ge_one ω hω.1 hω.2 S hS⟩

/-- The actual registered Wilson color law, with the true subtree and ray-tail
roots, assigns mass one to positive contact counts. -/
theorem actualWilson_contacts_positive (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (S : Finset (Site 2)) (hS : S.Nonempty) :
    ∀ᵐ σ ∂wilsonColorLaw (sourceConnectingPair ω hT hOne S hS).roots,
      1 ≤ contacts (connectingSites ω hT hOne S hS) σ := by
  let p := sourceConnectingPair ω hT hOne S hS
  have hcolor : ∀ᵐ f ∂(wilsonLaw p.roots : Measure ForestField),
      f.2 (p.ray.vertex 1) = true := by
    filter_upwards [wilsonLaw_ae_root_colors p.roots] with f hf
    exact hf.1 _ ⟨0, rfl⟩
  have hpos : ∀ᵐ f ∂(wilsonLaw p.roots : Measure ForestField),
      1 ≤ contacts p.sites f.2 := hcolor.mono (fun f hf => contacts_ge_one p f.2 hf)
  exact (ae_map_iff measurable_snd.aemeasurable
    ((continuous_contacts p.sites).measurable (measurableSet_Ici))).mpr hpos

end ConnectingConsumer

end
end FiniteAvalanches.Trees.Lattice

#check @FiniteAvalanches.Trees.Lattice.connectingSites_characterization
#check @FiniteAvalanches.Trees.Lattice.sourceConnectingPair_characterization
#print axioms FiniteAvalanches.Trees.Lattice.connectingSites_eq_span
#print axioms FiniteAvalanches.Trees.Lattice.existsUnique_connectingSites
#print axioms FiniteAvalanches.Trees.Lattice.sourceConnectingPair
#print axioms FiniteAvalanches.Trees.Lattice.sourceBoundaryCount_ge_one
#print axioms FiniteAvalanches.Trees.Lattice.connectingSites_singleton
#print axioms FiniteAvalanches.Trees.Lattice.connectingSites_pair
#print axioms FiniteAvalanches.Trees.Lattice.ConnectingConsumer.actualUST_connecting_objects
#print axioms FiniteAvalanches.Trees.Lattice.ConnectingConsumer.actualWilson_contacts_positive
