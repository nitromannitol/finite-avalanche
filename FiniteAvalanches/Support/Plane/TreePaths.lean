import FiniteAvalanches.Support.Plane.CompactAvoidance

/-!
Ported from Lattice-Probability `LatticeProb/Topology/PlaneGraph/TreePaths.lean` at commit `ba2b67f3`.

# Paths and polygonal attachments in finite arc trees

Distinct points of a finite planar arc tree can be joined by an injective path.
A polygonal arc tree can be extended by a simple polygonal path that meets it
only at its root.
-/

open Set
namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb

private theorem subpath_injective {X : Type*} [TopologicalSpace X] {a b : X}
    (p : Path a b) (hp : Function.Injective p) {s t : unitInterval} (hst : s ≠ t) :
    Function.Injective (p.subpath s t) := by
  intro u v huv
  have h := congrArg Subtype.val (hp huv)
  simp only [Set.Icc.coe_convexComb] at h
  have hst' : (s : ℝ) ≠ t := fun h => hst (Subtype.ext h)
  apply Subtype.ext
  have hz : ((u : ℝ) - v) * ((t : ℝ) - s) = 0 := by nlinarith [h]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr (Ne.symm hst')))

private theorem subpath_range_subset {X : Type*} [TopologicalSpace X] {a b : X}
    (p : Path a b) (s t : unitInterval) : range (p.subpath s t) ⊆ range p := by
  rw [Path.range_subpath]
  exact image_subset_range _ _

/-- Distinct points of a finite arc tree are joined by an injective path in the tree. -/
theorem IsFiniteArcTree.exists_injective_path {r : ℝ × ℝ} {K : Set (ℝ × ℝ)}
    (hK : IsFiniteArcTree r K) {a b : ℝ × ℝ} (ha : a ∈ K) (hb : b ∈ K)
    (hab : a ≠ b) : ∃ q : Path a b, Function.Injective q ∧ range q ⊆ K := by
  induction hK generalizing a b with
  | singleton =>
      simp only [mem_singleton_iff] at ha hb
      exact (hab (ha.trans hb.symm)).elim
  | @attach K x z p hK hp hinter ih =>
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · obtain ⟨s, rfl⟩ := ha
        obtain ⟨t, rfl⟩ := hb
        have hst : s ≠ t := fun h => hab (congrArg p h)
        exact ⟨p.subpath s t, subpath_injective p hp hst,
          (subpath_range_subset p s t).trans (subset_union_left)⟩
      · obtain ⟨s, rfl⟩ := ha
        have hzK : z ∈ K := by
          have hz : z ∈ range p ∩ K := by rw [hinter]; exact mem_singleton z
          exact hz.2
        by_cases hasK : p s ∈ K
        · obtain ⟨w, hw, hwsub⟩ := ih hasK hb hab
          exact ⟨w, hw, hwsub.trans subset_union_right⟩
        by_cases hbz : b = z
        · subst b
          have hst : s ≠ 1 := by
            intro h
            apply hab
            simp only [h, Path.target]
          let q : Path (p s) z := (p.subpath s 1).cast rfl p.target.symm
          exact ⟨q, subpath_injective p hp hst,
            (subpath_range_subset p s 1).trans subset_union_left⟩
        · have hpz : p s ≠ z := fun heq => hasK (heq.symm ▸ hzK)
          have hst : s ≠ 1 := by
            intro h
            apply hpz
            simp only [h, Path.target]
          let q : Path (p s) z := (p.subpath s 1).cast rfl p.target.symm
          obtain ⟨w, hw, hwsub⟩ := ih hzK hb (Ne.symm hbz)
          have hqsub : range q ⊆ range p := subpath_range_subset p s 1
          have hmeet : range q ∩ range w = {z} := by
            apply subset_antisymm
            · intro y hy
              have hy' : y ∈ range p ∩ K := ⟨hqsub hy.1, hwsub hy.2⟩
              rw [hinter] at hy'
              exact hy'
            · intro y hy
              simp only [mem_singleton_iff] at hy
              subst y
              exact ⟨q.target_mem_range, w.source_mem_range⟩
          exact ⟨q.trans w, LatticeProb.Topology.path_trans_injective
            (subpath_injective p hp hst) hw hmeet, by
              rw [Path.trans_range]
              exact union_subset (hqsub.trans subset_union_left) (hwsub.trans subset_union_right)⟩
      · obtain ⟨t, rfl⟩ := hb
        have hzK : z ∈ K := by
          have hz : z ∈ range p ∩ K := by rw [hinter]; exact mem_singleton z
          exact hz.2
        by_cases hbtK : p t ∈ K
        · obtain ⟨w, hw, hwsub⟩ := ih ha hbtK hab
          exact ⟨w, hw, hwsub.trans subset_union_right⟩
        by_cases haz : a = z
        · subst a
          have hst : (1 : unitInterval) ≠ t := by
            intro h
            apply hab
            simp only [← h, Path.target]
          let q : Path z (p t) := (p.subpath 1 t).cast p.target.symm rfl
          exact ⟨q, subpath_injective p hp hst,
            (subpath_range_subset p 1 t).trans subset_union_left⟩
        · have hpz : p t ≠ z := fun heq => hbtK (heq.symm ▸ hzK)
          have hst : (1 : unitInterval) ≠ t := by
            intro h
            apply hpz
            simp only [← h, Path.target]
          let q : Path z (p t) := (p.subpath 1 t).cast p.target.symm rfl
          obtain ⟨w, hw, hwsub⟩ := ih ha hzK haz
          have hqsub : range q ⊆ range p := subpath_range_subset p 1 t
          have hmeet : range w ∩ range q = {z} := by
            apply subset_antisymm
            · intro y hy
              have hy' : y ∈ range p ∩ K := ⟨hqsub hy.2, hwsub hy.1⟩
              rw [hinter] at hy'
              exact hy'
            · intro y hy
              simp only [mem_singleton_iff] at hy
              subst y
              exact ⟨w.target_mem_range, q.source_mem_range⟩
          exact ⟨w.trans q, LatticeProb.Topology.path_trans_injective hw
            (subpath_injective p hp hst) hmeet, by
              rw [Path.trans_range]
              exact union_subset (hwsub.trans subset_union_right) (hqsub.trans subset_union_left)⟩
      · obtain ⟨q, hq, hsub⟩ := ih ha hb hab
        exact ⟨q, hq, hsub.trans subset_union_right⟩
/-- A finite family of simple paths meeting pairwise only at their common endpoint
forms a finite arc tree. The singleton also covers the empty family. -/
theorem isFiniteArcTree_finset_paths {ι : Type*} (s : Finset ι)
    {r : ℝ × ℝ} {x : ι → ℝ × ℝ} (p : ∀ i, Path (x i) r)
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → range (p i) ∩ range (p j) = {r}) :
    IsFiniteArcTree r ({r} ∪ ⋃ i ∈ s, range (p i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (IsFiniteArcTree.singleton : IsFiniteArcTree r {r})
  | @insert i s hi ih =>
      have ht := ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))
        (fun j hj k hk hne => hd j (Finset.mem_insert_of_mem hj)
          k (Finset.mem_insert_of_mem hk) hne)
      have hinter : range (p i) ∩ ({r} ∪ ⋃ j ∈ s, range (p j)) = {r} := by
        ext z
        constructor
        · rintro ⟨hzi, hzr | hzr⟩
          · exact hzr
          · obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp hzr
            rw [← hd i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
              (fun h => hi (h ▸ hj))]
            exact ⟨hzi, hzj⟩
        · intro hz
          have hz' : z = r := mem_singleton_iff.mp hz
          subst z
          exact ⟨(p i).target_mem_range, Or.inl (mem_singleton r)⟩
      have htree := IsFiniteArcTree.attach (p i) ht
        (hp i (Finset.mem_insert_self i s)) hinter
      convert htree using 1
      ext z
      simp only [mem_union, mem_singleton_iff, mem_iUnion, Finset.mem_insert]
      aesop

/-- Removing a finite star of simple paths from an open connected plane region
preserves preconnectedness. -/
theorem isPreconnected_sdiff_finset_star {ι : Type*} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U) (s : Finset ι)
    {r : ℝ × ℝ} {x : ι → ℝ × ℝ} (p : ∀ i, Path (x i) r)
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → range (p i) ∩ range (p j) = {r})
    (hr : r ∈ U) (hsub : ∀ i ∈ s, range (p i) ⊆ U) :
    IsPreconnected (U \ ({r} ∪ ⋃ i ∈ s, range (p i))) := by
  have ht := isFiniteArcTree_finset_paths s p hp hd
  apply isPreconnected_sdiff_nonseparating_compact hU hconn ht.isCompact ht.not_separates
  exact union_subset (singleton_subset_iff.mpr hr) (iUnion₂_subset hsub)

/-- A finite collection of nonzero planar vectors admits a nonparallel direction. -/
theorem exists_direction_not_parallel {S : Set (ℝ × ℝ)} (hS : S.Finite) :
    ∃ d : ℝ × ℝ, d ≠ 0 ∧ ∀ v ∈ S, v ≠ 0 → d.1 * v.2 - d.2 * v.1 ≠ 0 := by
  let slopes : Set ℝ := (fun v : ℝ × ℝ => v.2 / v.1) '' S
  have hslopes : slopes.Finite := hS.image _
  obtain ⟨t, _, ht⟩ := (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).exists_notMem_finite hslopes
  refine ⟨(1, t), by simp, ?_⟩
  intro v hv hv0 hdet
  by_cases hv1 : v.1 = 0
  · have hv2 : v.2 = 0 := by simp [hv1] at hdet; exact hdet
    apply hv0
    exact Prod.ext hv1 hv2
  · have ht' : t = v.2 / v.1 := by
      apply (eq_div_iff hv1).2
      simp only [one_mul] at hdet
      linarith
    apply ht
    exact ⟨v, hv, ht'.symm⟩

/-- Inside an open neighborhood, a nondegenerate segment can be chosen with
direction nonparallel to any prescribed finite collection of vectors. -/
theorem exists_segment_not_parallel {U S : Set (ℝ × ℝ)} (hU : IsOpen U)
    {r : ℝ × ℝ} (hr : r ∈ U) (hS : S.Finite) :
    ∃ q : ℝ × ℝ, q ≠ r ∧ segment ℝ r q ⊆ U ∧
      ∀ v ∈ S, v ≠ 0 → (q - r).1 * v.2 - (q - r).2 * v.1 ≠ 0 := by
  obtain ⟨d, hd0, hd⟩ := exists_direction_not_parallel hS
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU r hr
  let f : ℝ → ℝ × ℝ := fun t => r + t • d
  have hf : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
  have hzero : (0 : ℝ) ∈ f ⁻¹' Metric.ball r ε := by
    simpa [f] using (Metric.mem_ball_self hε : r ∈ Metric.ball r ε)
  obtain ⟨δ, hδ, hδball⟩ := Metric.isOpen_iff.mp
    ((Metric.isOpen_ball : IsOpen (Metric.ball r ε)).preimage hf) 0 hzero
  have hδmem : δ / 2 ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
    linarith
  let q := f (δ / 2)
  have hqball : q ∈ Metric.ball r ε := hδball hδmem
  have hscale : (δ / 2 : ℝ) ≠ 0 := (half_pos hδ).ne'
  refine ⟨q, ?_, (convex_ball r ε).segment_subset (Metric.mem_ball_self hε) hqball |>.trans hball, ?_⟩
  · intro h
    have hz : (δ / 2 : ℝ) • d = 0 := by
      have := h
      dsimp [q, f] at this
      exact add_left_cancel (this.trans (add_zero r).symm)
    exact hd0 ((smul_eq_zero.mp hz).resolve_left hscale)
  · intro v hv hv0
    have hdet := hd v hv hv0
    dsimp [q, f]
    simp only [add_sub_cancel_left]
    have heq : δ / 2 * d.1 * v.2 - δ / 2 * d.2 * v.1 =
        δ / 2 * (d.1 * v.2 - d.2 * v.1) := by ring
    rw [heq]
    exact mul_ne_zero hscale hdet

/-- A simple path ending at a tree root can be extended from an exterior point
while meeting the tree only at the root. -/
theorem exists_path_to_root_of_stub {U K S : Set (ℝ × ℝ)} {r q x : ℝ × ℝ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hK : IsFiniteArcTree r K)
    (hKU : K ⊆ U) (hS : S.Finite) (p : Path q r) (hp : Function.Injective p)
    (hpU : range p ⊆ U \ S) (hpK : range p ∩ K = {r})
    (hx : x ∈ ((U \ K) \ S) \ range p) (hq : q ∉ K) :
    ∃ w : Path x r, Function.Injective w ∧ range w ⊆ U \ S ∧
      range w ∩ K = {r} := by
  have hKopen : IsOpen (U \ K) := hU.sdiff hK.isCompact.isClosed
  have hKconn : IsPreconnected (U \ K) :=
    isPreconnected_sdiff_nonseparating_compact hU hconn hK.isCompact hK.not_separates hKU
  have hq' : q ∈ ((U \ K) \ S) ∩ range p := by
    have h := hpU p.source_mem_range
    exact ⟨⟨⟨h.1, hq⟩, h.2⟩, p.source_mem_range⟩
  obtain ⟨z, hz, v, hv, hvsub, hvmeet⟩ :=
    exists_path_to_closed_set_avoiding_finite hKopen hKconn
      (isCompact_range p.continuous).isClosed hS hx hq'
  obtain ⟨t, rfl⟩ := hz
  have htK : p t ∉ K := (hvsub v.target_mem_range).1.2
  have ht : t ≠ 1 := by
    intro ht
    apply htK
    rw [ht, p.target]
    have : r ∈ range p ∩ K := by rw [hpK]; exact mem_singleton r
    exact this.2
  let w : Path (p t) r := (p.subpath t 1).cast rfl p.target.symm
  have hwsub : range w ⊆ range p := subpath_range_subset p t 1
  have hmeet : range v ∩ range w = {p t} := by
    apply subset_antisymm
    · intro y hy
      rw [← hvmeet]
      exact ⟨hy.1, hwsub hy.2⟩
    · intro y hy
      simp only [mem_singleton_iff] at hy
      subst y
      exact ⟨v.target_mem_range, w.source_mem_range⟩
  refine ⟨v.trans w, LatticeProb.Topology.path_trans_injective hv
    (subpath_injective p hp ht) hmeet, ?_, ?_⟩
  · rw [Path.trans_range]
    exact union_subset (fun y hy => ⟨(hvsub hy).1.1, (hvsub hy).2⟩) (hwsub.trans hpU)
  · rw [Path.trans_range]
    apply subset_antisymm
    · rintro y ⟨hy | hy, hyK⟩
      · exact ((hvsub hy).1.2 hyK).elim
      · rw [← hpK]
        exact ⟨hwsub hy, hyK⟩
    · intro y hy
      simp only [mem_singleton_iff] at hy
      subst y
      refine ⟨Or.inr w.target_mem_range, ?_⟩
      have : r ∈ range p ∩ K := by rw [hpK]; exact mem_singleton r
      exact this.2

end FiniteAvalanches.Electrical.StatementGeometry

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb

open Source BSST

/-- Arc trees in disjoint faces provide injective paths to their marked points. -/
theorem exists_face_injective_paths_of_arcTrees
    {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}
    (D : Drawing J) (r : Face D → ℝ × ℝ) (K : Face D → Set (ℝ × ℝ))
    (A : Face D → Finset (ℝ × ℝ))
    (hK : ∀ F, IsFiniteArcTree (r F) (K F))
    (hroot : ∀ F, r F ∈ K F) (hsub : ∀ F, K F ⊆ faceRegion D F)
    (hrA : ∀ F, r F ∉ A F) (hA : ∀ F z, z ∈ A F → z ∈ K F) :
    ∃ p : ∀ F (z : {z // z ∈ A F}), Path (r F) z.1,
      (∀ F z, Function.Injective (p F z) ∧ range (p F z) ⊆ K F) ∧
      ∀ F G, F ≠ G → ∀ z w, Disjoint (range (p F z)) (range (p G w)) := by
  have hex : ∀ F (z : {z // z ∈ A F}),
      ∃ p : Path (r F) z.1, Function.Injective p ∧ range p ⊆ K F := by
    intro F z
    exact (hK F).exists_injective_path (hroot F) (hA F z.1 z.2)
      (fun heq => hrA F (heq.symm ▸ z.2))
  choose p hp using hex
  refine ⟨p, hp, ?_⟩
  intro F G hFG z w
  exact (faceRegion_disjoint D hFG).mono
    ((hp F z).2.trans (hsub F)) ((hp G w).2.trans (hsub G))

end FiniteAvalanches.Electrical.StatementGeometry

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb

/-- A path that lies in a set except at its endpoint meets the complement
exactly at that endpoint. -/
theorem range_inter_compl_of_mem_except_target
    {X : Type*} [TopologicalSpace X] {U : Set X} {x y : X} (p : Path x y)
    (hp : ∀ t : unitInterval, t ≠ 1 → p t ∈ U) (hy : y ∉ U) :
    range p ∩ Uᶜ = {y} := by
  ext z
  constructor
  · rintro ⟨⟨t, rfl⟩, ht⟩
    have ht1 : t = 1 := by
      by_contra hne
      exact ht (hp t hne)
    simpa only [ht1, Path.target] using (mem_singleton y)
  · intro hz
    have hz' : z = y := mem_singleton_iff.mp hz
    subst z
    exact ⟨p.target_mem_range, hy⟩

/-- A path whose only point outside a region is its endpoint meets the
complement of that region in a preconnected set. -/
theorem isPreconnected_range_inter_compl_of_mem_except_target
    {X : Type*} [TopologicalSpace X] {U : Set X} {x y : X} (p : Path x y)
    (hp : ∀ t : unitInterval, t ≠ 1 → p t ∈ U) (hy : y ∉ U) :
    IsPreconnected (range p ∩ Uᶜ) := by
  rw [range_inter_compl_of_mem_except_target p hp hy]
  exact isPreconnected_singleton

/-- Two simple paths ending at the same boundary point form a simple path
whose intersection with the complement of the region is that point. -/
theorem paired_boundary_paths {X : Type*} [TopologicalSpace X] {U : Set X}
    {x y z : X} (p : Path x z) (q : Path y z)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hmeet : range p ∩ range q = {z})
    (hpU : ∀ t : unitInterval, t ≠ 1 → p t ∈ U)
    (hqU : ∀ t : unitInterval, t ≠ 1 → q t ∈ U) (hz : z ∉ U) :
    Function.Injective (p.trans q.symm) ∧
      range (p.trans q.symm) ∩ Uᶜ = {z} := by
  have hq' : Function.Injective q.symm := by
    intro a b h
    exact unitInterval.symm_involutive.injective (hq h)
  constructor
  · apply LatticeProb.Topology.path_trans_injective hp hq'
    simpa only [Path.symm_range] using hmeet
  · rw [Path.trans_range, Path.symm_range, union_inter_distrib_right,
      range_inter_compl_of_mem_except_target p hpU hz,
      range_inter_compl_of_mem_except_target q hqU hz, union_self]

/-- Removing finitely many simple arcs preserves preconnectedness when they
are disjoint inside the region and each meets its complement in a
preconnected set. -/
theorem isPreconnected_sdiff_finset_paths_of_disjoint_inside
    {ι : Type*} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hconn : IsPreconnected U)
    (s : Finset ι) {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (p i) ∩ U) (range (p j)))
    (hinter : ∀ i ∈ s, IsPreconnected (range (p i) ∩ Uᶜ)) :
    IsPreconnected (U \ (⋃ i ∈ s, range (p i))) := by
  classical
  open QuantumZipper.CA.Topo MatedCRTHarmonic.Topology in
  induction s using Finset.induction_on with
  | empty => simpa using hconn
  | @insert i s hi ih =>
      have hc : IsCompact (⋃ j ∈ s, range (p j)) :=
        s.isCompact_biUnion (fun j _ => isCompact_range (p j).continuous)
      have hprev := ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))
        (fun j hj k hk hne => hd j (Finset.mem_insert_of_mem hj)
          k (Finset.mem_insert_of_mem hk) hne)
        (fun j hj => hinter j (Finset.mem_insert_of_mem hj))
      have hinter' : range (p i) ∩ (U \ (⋃ j ∈ s, range (p j)))ᶜ =
          range (p i) ∩ Uᶜ := by
        ext z
        constructor
        · rintro ⟨hzi, hn⟩
          refine ⟨hzi, fun hzU => hn ⟨hzU, ?_⟩⟩
          intro hzs
          obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp hzs
          exact Set.disjoint_left.mp (hd i (Finset.mem_insert_self i s) j
            (Finset.mem_insert_of_mem hj) (fun h => hi (h ▸ hj))) ⟨hzi, hzU⟩ hzj
        · rintro ⟨hzi, hzU⟩
          exact ⟨hzi, fun hz => hzU hz.1⟩
      have hsep := not_separates_image_finset_paths {i} p
        (by simpa using hp i (Finset.mem_insert_self i s)) (by simp)
      have hsep' : ∀ ⦃a b : ℂ⦄,
          a ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' range (p i) →
          b ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' range (p i) →
          ¬ Separates (Complex.equivRealProdCLM.symm.toHomeomorph '' range (p i)) a b := by
        simpa using hsep
      have hnew : IsPreconnected ((U \ (⋃ j ∈ s, range (p j))) \ range (p i)) :=
        isPreconnected_sdiff_nonseparating_compact_of_preconnected_inter_compl
          (hU.sdiff hc.isClosed) hprev (isCompact_range (p i).continuous) hsep'
          (hinter' ▸ hinter i (Finset.mem_insert_self i s))
      convert hnew using 1
      ext z
      simp only [mem_sdiff, mem_iUnion, Finset.mem_insert]
      constructor
      · rintro ⟨hzU, hn⟩
        refine ⟨⟨hzU, ?_⟩, ?_⟩
        · rintro ⟨j, hj, hzj⟩
          exact hn ⟨j, Or.inr hj, hzj⟩
        · intro hzi
          exact hn ⟨i, Or.inl rfl, hzi⟩
      · rintro ⟨⟨hzU, hs⟩, hzi⟩
        refine ⟨hzU, ?_⟩
        rintro ⟨j, hj, hzj⟩
        rcases hj with rfl | hj
        · exact hzi hzj
        · exact hs ⟨j, hj, hzj⟩

/-- A point can reach one of finitely many disjoint arcs without meeting the
others, and meets the chosen arc only at the end of the path. -/
theorem exists_path_first_hit_avoiding_finset_paths
    {ι : Type*} [DecidableEq ι] {U T : Set (ℝ × ℝ)} (hU : IsOpen U) (hconn : IsPreconnected U)
    (s : Finset ι) {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (range (p i)) (range (p j)))
    (hsub : ∀ i ∈ s, range (p i) ⊆ U) (hT : T.Finite)
    {r a : ℝ × ℝ} (hr : r ∈ (U \ (⋃ i ∈ s, range (p i))) \ T)
    {i : ι} (hi : i ∈ s) (ha : a ∈ range (p i) \ T) :
    ∃ z ∈ range (p i), ∃ q : Path r z, Function.Injective q ∧
      range q ⊆ (U \ (⋃ j ∈ s.erase i, range (p j))) \ T ∧
      range q ∩ range (p i) = {z} := by
  classical
  let A : Set (ℝ × ℝ) := ⋃ j ∈ s.erase i, range (p j)
  have hcompact : IsCompact A :=
    (s.erase i).isCompact_biUnion (fun j _ => isCompact_range (p j).continuous)
  have hpre : IsPreconnected (U \ A) :=
    isPreconnected_sdiff_finset_paths hU hconn (s.erase i) p
      (fun j hj => hp j (Finset.mem_of_mem_erase hj))
      (fun j hj k hk hne => hd j (Finset.mem_of_mem_erase hj)
        k (Finset.mem_of_mem_erase hk) hne)
      (fun j hj => hsub j (Finset.mem_of_mem_erase hj))
  have hr' : r ∈ ((U \ A) \ T) \ range (p i) := by
    refine ⟨⟨⟨hr.1.1, ?_⟩, hr.2⟩, ?_⟩
    · intro h
      obtain ⟨j, hj, hjr⟩ := mem_iUnion₂.mp h
      exact hr.1.2 (mem_iUnion₂.mpr ⟨j, Finset.mem_of_mem_erase hj, hjr⟩)
    · intro h
      exact hr.1.2 (mem_iUnion₂.mpr ⟨i, hi, h⟩)
  have ha' : a ∈ ((U \ A) \ T) ∩ range (p i) := by
    refine ⟨⟨⟨hsub i hi ha.1, ?_⟩, ha.2⟩, ha.1⟩
    intro h
    obtain ⟨j, hj, hja⟩ := mem_iUnion₂.mp h
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    exact (Set.disjoint_left.mp (hd j (Finset.mem_of_mem_erase hj) i hi hji)) hja ha.1
  exact exists_path_to_closed_set_avoiding_finite (hU.sdiff hcompact.isClosed)
    hpre (isCompact_range (p i).continuous).isClosed hT hr' ha'


/-- A point can reach one of finitely many disjoint arcs without meeting the
others, when each arc meets the complement of the region in a preconnected set. -/
theorem exists_path_first_hit_avoiding_boundary_paths
    {ι : Type*} [DecidableEq ι] {U T : Set (ℝ × ℝ)} (hU : IsOpen U) (hconn : IsPreconnected U)
    (s : Finset ι) {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (range (p i)) (range (p j)))
    (hsub : ∀ i ∈ s, IsPreconnected (range (p i) ∩ Uᶜ)) (hT : T.Finite)
    {r a : ℝ × ℝ} (hr : r ∈ (U \ (⋃ i ∈ s, range (p i))) \ T)
    {i : ι} (hi : i ∈ s) (ha : a ∈ (range (p i) ∩ U) \ T) :
    ∃ z ∈ range (p i), ∃ q : Path r z, Function.Injective q ∧
      range q ⊆ (U \ (⋃ j ∈ s.erase i, range (p j))) \ T ∧
      range q ∩ range (p i) = {z} := by
  classical
  let A : Set (ℝ × ℝ) := ⋃ j ∈ s.erase i, range (p j)
  have hcompact : IsCompact A :=
    (s.erase i).isCompact_biUnion (fun j _ => isCompact_range (p j).continuous)
  have hpre : IsPreconnected (U \ A) :=
    isPreconnected_sdiff_finset_paths_of_preconnected_inter_compl hU hconn (s.erase i) p
      (fun j hj => hp j (Finset.mem_of_mem_erase hj))
      (fun j hj k hk hne => hd j (Finset.mem_of_mem_erase hj)
        k (Finset.mem_of_mem_erase hk) hne)
      (fun j hj => hsub j (Finset.mem_of_mem_erase hj))
  have hr' : r ∈ ((U \ A) \ T) \ range (p i) := by
    refine ⟨⟨⟨hr.1.1, ?_⟩, hr.2⟩, ?_⟩
    · intro h
      obtain ⟨j, hj, hjr⟩ := mem_iUnion₂.mp h
      exact hr.1.2 (mem_iUnion₂.mpr ⟨j, Finset.mem_of_mem_erase hj, hjr⟩)
    · intro h
      exact hr.1.2 (mem_iUnion₂.mpr ⟨i, hi, h⟩)
  have ha' : a ∈ ((U \ A) \ T) ∩ range (p i) := by
    refine ⟨⟨⟨ha.1.2, ?_⟩, ha.2⟩, ha.1.1⟩
    intro h
    obtain ⟨j, hj, hja⟩ := mem_iUnion₂.mp h
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    exact (Set.disjoint_left.mp (hd j (Finset.mem_of_mem_erase hj) i hi hji)) hja ha.1.1
  exact exists_path_to_closed_set_avoiding_finite (hU.sdiff hcompact.isClosed)
    hpre (isCompact_range (p i).continuous).isClosed hT hr' ha'

/-- A point can reach one of finitely many arcs while avoiding the others if
the arcs are disjoint within the region and meet its complement in
preconnected sets. -/
theorem exists_path_first_hit_avoiding_paths_disjoint_inside
    {ι : Type*} [DecidableEq ι] {U T : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (s : Finset ι) {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (p i) ∩ U) (range (p j)))
    (hsub : ∀ i ∈ s, IsPreconnected (range (p i) ∩ Uᶜ)) (hT : T.Finite)
    {r a : ℝ × ℝ} (hr : r ∈ (U \ (⋃ i ∈ s, range (p i))) \ T)
    {i : ι} (hi : i ∈ s) (ha : a ∈ (range (p i) ∩ U) \ T) :
    ∃ z ∈ range (p i), ∃ q : Path r z, Function.Injective q ∧
      range q ⊆ (U \ (⋃ j ∈ s.erase i, range (p j))) \ T ∧
      range q ∩ range (p i) = {z} := by
  classical
  let A : Set (ℝ × ℝ) := ⋃ j ∈ s.erase i, range (p j)
  have hcompact : IsCompact A :=
    (s.erase i).isCompact_biUnion (fun j _ => isCompact_range (p j).continuous)
  have hpre : IsPreconnected (U \ A) :=
    isPreconnected_sdiff_finset_paths_of_disjoint_inside hU hconn (s.erase i) p
      (fun j hj => hp j (Finset.mem_of_mem_erase hj))
      (fun j hj k hk hne => hd j (Finset.mem_of_mem_erase hj)
        k (Finset.mem_of_mem_erase hk) hne)
      (fun j hj => hsub j (Finset.mem_of_mem_erase hj))
  have hr' : r ∈ ((U \ A) \ T) \ range (p i) := by
    refine ⟨⟨⟨hr.1.1, ?_⟩, hr.2⟩, ?_⟩
    · intro h
      obtain ⟨j, hj, hjr⟩ := mem_iUnion₂.mp h
      exact hr.1.2 (mem_iUnion₂.mpr ⟨j, Finset.mem_of_mem_erase hj, hjr⟩)
    · intro h
      exact hr.1.2 (mem_iUnion₂.mpr ⟨i, hi, h⟩)
  have ha' : a ∈ ((U \ A) \ T) ∩ range (p i) := by
    refine ⟨⟨⟨ha.1.2, ?_⟩, ha.2⟩, ha.1.1⟩
    intro h
    obtain ⟨j, hj, hja⟩ := mem_iUnion₂.mp h
    exact Set.disjoint_left.mp (hd i hi j (Finset.mem_of_mem_erase hj)
      (Ne.symm (Finset.mem_erase.mp hj).1)) ha.1 hja
  exact exists_path_to_closed_set_avoiding_finite (hU.sdiff hcompact.isClosed)
    hpre (isCompact_range (p i).continuous).isClosed hT hr' ha'

/-- A point can reach the boundary endpoint of a chosen arc while avoiding a
finite set and the other arcs inside the region, following a final subarc. -/
theorem exists_path_to_boundary_avoiding_paths_disjoint_inside_and_finite
    {ι : Type*} [DecidableEq ι] {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (s : Finset ι) {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (p i) ∩ U) (range (p j)))
    (hinside : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → p i t ∈ U)
    (hout : ∀ i ∈ s, y i ∉ U)
    {S : Set (ℝ × ℝ)} (hS : S.Finite)
    (hobsS : ∀ j ∈ s, Disjoint (range (p j)) S)
    {r : ℝ × ℝ} (hr : r ∈ (U \ (⋃ i ∈ s, range (p i))) \ S)
    {i : ι} (hi : i ∈ s) :
    ∃ q : Path r (y i), Function.Injective q ∧
      Disjoint (range q) S ∧ range q ∩ Uᶜ = {y i} ∧
      Disjoint (range q ∩ U) (⋃ j ∈ s.erase i, range (p j)) ∧
      ∃ t : unitInterval, t ≠ 1 ∧ range ((p i).subpath t 1) ⊆ range q := by
  classical
  have hcomp : ∀ j ∈ s, IsPreconnected (range (p j) ∩ Uᶜ) :=
    fun j hj => isPreconnected_range_inter_compl_of_mem_except_target
      (p j) (hinside j hj) (hout j hj)
  have ha : p i 0 ∈ (range (p i) ∩ U) \ S :=
    ⟨⟨⟨0, rfl⟩, hinside i hi 0 (by norm_num)⟩,
      fun h => Set.disjoint_left.mp (hobsS i hi) ⟨0, rfl⟩ h⟩
  obtain ⟨z, ⟨t, ht⟩, q, hq, hqsub, hmeet⟩ :=
    exists_path_first_hit_avoiding_paths_disjoint_inside hU hconn s p hp hd hcomp
      hS hr hi ha
  have hzU : z ∈ U := (hqsub q.target_mem_range).1.1
  have ht1 : t ≠ 1 := by
    intro ht1
    apply hout i hi
    rw [← ht] at hzU
    simpa only [ht1, Path.target] using hzU
  let w : Path z (y i) := ((p i).subpath t 1).cast ht.symm (p i).target.symm
  have hwsub : range w ⊆ range (p i) := subpath_range_subset (p i) t 1
  have hw : Function.Injective w := subpath_injective (p i) (hp i hi) ht1
  have hqw : range q ∩ range w = {z} := by
    apply subset_antisymm
    · intro v hv
      rw [← hmeet]
      exact ⟨hv.1, hwsub hv.2⟩
    · exact singleton_subset_iff.mpr ⟨q.target_mem_range, w.source_mem_range⟩
  refine ⟨q.trans w, LatticeProb.Topology.path_trans_injective hq hw hqw, ?_, ?_, ?_, ?_⟩
  · rw [Path.trans_range]
    exact disjoint_union_left.mpr ⟨Set.disjoint_left.mpr (fun _ hz hs => (hqsub hz).2 hs),
      (hobsS i hi).mono_left hwsub⟩
  · rw [Path.trans_range, union_inter_distrib_right]
    have hqU : range q ∩ Uᶜ = ∅ := by
      apply subset_antisymm ?_ (empty_subset _)
      rintro v ⟨hv, hvU⟩
      exact hvU (hqsub hv).1.1
    rw [hqU, empty_union]
    apply subset_antisymm
    · intro v hv
      rw [← range_inter_compl_of_mem_except_target (p i) (hinside i hi) (hout i hi)]
      exact ⟨hwsub hv.1, hv.2⟩
    · exact singleton_subset_iff.mpr ⟨w.target_mem_range, hout i hi⟩
  · apply Set.disjoint_left.mpr
    rintro v ⟨hv, hvU⟩ hvobs
    rw [Path.trans_range] at hv
    rcases hv with hv | hv
    · exact (hqsub hv).1.2 hvobs
    · obtain ⟨j, hj, hvj⟩ := mem_iUnion₂.mp hvobs
      exact Set.disjoint_left.mp (hd i hi j (Finset.mem_of_mem_erase hj)
        (Ne.symm (Finset.mem_erase.mp hj).1)) ⟨hwsub hv, hvU⟩ hvj
  · refine ⟨t, ht1, ?_⟩
    rw [Path.trans_range]
    exact subset_union_right

/-- Boundary access avoiding a finite family of paths disjoint inside the region. -/
theorem exists_path_to_boundary_avoiding_paths_disjoint_inside
    {ι : Type*} [DecidableEq ι] {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (s : Finset ι) {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (p i) ∩ U) (range (p j)))
    (hinside : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → p i t ∈ U)
    (hout : ∀ i ∈ s, y i ∉ U)
    {r : ℝ × ℝ} (hr : r ∈ U \ (⋃ i ∈ s, range (p i)))
    {i : ι} (hi : i ∈ s) :
    ∃ q : Path r (y i), Function.Injective q ∧
      range q ∩ Uᶜ = {y i} ∧
      Disjoint (range q ∩ U) (⋃ j ∈ s.erase i, range (p j)) ∧
      ∃ t : unitInterval, t ≠ 1 ∧ range ((p i).subpath t 1) ⊆ range q := by
  obtain ⟨q, hq, _, hboundary, havoid, htail⟩ :=
    exists_path_to_boundary_avoiding_paths_disjoint_inside_and_finite hU hconn s p hp hd
      hinside hout (S := ∅) Set.finite_empty (by simp) ⟨hr, by simp⟩ hi
  exact ⟨q, hq, hboundary, havoid, htail⟩

end FiniteAvalanches.Electrical.StatementGeometry

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb

private theorem segment_inter_eq_singleton_of_det_ne {r q v : ℝ × ℝ}
    (hdet : (q-r).1 * (v-r).2 - (q-r).2 * (v-r).1 ≠ 0) :
    segment ℝ r q ∩ segment ℝ r v = {r} := by
  apply subset_antisymm
  · rintro x ⟨hx, hy⟩
    rw [segment_eq_image' ℝ r q] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [segment_eq_image' ℝ r v] at hy
    obtain ⟨b, hb, h⟩ := hy
    dsimp only at h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    change r.1 + b * (v-r).1 = r.1 + a * (q-r).1 at h1
    change r.2 + b * (v-r).2 = r.2 + a * (q-r).2 at h2
    have ha0 : a = 0 := by
      by_contra hane
      apply hdet
      have hh1 : b * (v-r).1 = a * (q-r).1 := by linarith [h1]
      have hh2 : b * (v-r).2 = a * (q-r).2 := by linarith [h2]
      have hz : a * ((q-r).1 * (v-r).2 - (q-r).2 * (v-r).1) = 0 := by
        calc
          _ = (b * (v-r).1) * (v-r).2 - (b * (v-r).2) * (v-r).1 := by rw [hh1, hh2]; ring
          _ = 0 := by ring
      exact (mul_eq_zero.mp hz).resolve_left hane
    simp only [ha0, zero_smul, add_zero, mem_singleton_iff]
  · exact singleton_subset_iff.mpr ⟨left_mem_segment ℝ r q, left_mem_segment ℝ r v⟩

/-- A short segment can avoid any obstacle that is locally contained in finitely
many segments starting at the base point. -/
theorem exists_segment_avoiding_locally_radial {U W K S : Set (ℝ × ℝ)}
    {r : ℝ × ℝ} (hU : IsOpen U) (hW : IsOpen W) (hrU : r ∈ U) (hrW : r ∈ W)
    (hrK : r ∈ K) (hS : S.Finite)
    (hlocal : K ∩ W ⊆ ⋃ v ∈ S, segment ℝ r v) :
    ∃ q : ℝ × ℝ, q ≠ r ∧ segment ℝ r q ⊆ U ∧
      segment ℝ r q ∩ K = {r} := by
  have hS' : ((fun v : ℝ × ℝ => v - r) '' (S \ {r})).Finite :=
    (hS.subset sdiff_subset).image _
  obtain ⟨q, hqr, hseg, hdet⟩ := exists_segment_not_parallel (hU.inter hW) ⟨hrU, hrW⟩ hS'
  refine ⟨q, hqr, hseg.trans inter_subset_left, ?_⟩
  apply subset_antisymm
  · intro x hx
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp (hlocal ⟨hx.2, (hseg hx.1).2⟩)
    by_cases hvr : v = r
    · subst v
      simpa only [segment_same, mem_singleton_iff] using hxv
    · have hd := hdet (v-r) ⟨v, ⟨hv, by simpa using hvr⟩, rfl⟩ (sub_ne_zero.mpr hvr)
      rw [← segment_inter_eq_singleton_of_det_ne hd]
      exact ⟨hx.1, hxv⟩
  · exact singleton_subset_iff.mpr ⟨left_mem_segment ℝ r q, hrK⟩

private theorem segment_subset_segments_at {a b r : ℝ × ℝ} (hr : r ∈ segment ℝ a b) :
    segment ℝ a b ⊆ segment ℝ r a ∪ segment ℝ r b := by
  rw [segment_eq_image_lineMap] at hr
  obtain ⟨t, ht, rfl⟩ := hr
  intro x hx
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  have hs' : s ∈ Set.uIcc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hs
  rcases Set.uIcc_subset_uIcc_union_uIcc hs' with hs | hs
  · have h := image_segment ℝ (AffineMap.lineMap a b) 0 t
    rw [AffineMap.lineMap_apply_zero] at h
    apply Or.inl
    rw [segment_symm, ← h]
    exact ⟨s, by simpa only [segment_eq_uIcc] using hs, rfl⟩
  · have h := image_segment ℝ (AffineMap.lineMap a b) t 1
    rw [AffineMap.lineMap_apply_one] at h
    apply Or.inr
    rw [← h]
    exact ⟨s, by simpa only [segment_eq_uIcc] using hs, rfl⟩

/-- A finite union of segments has an escaping segment at each of its points. -/
theorem exists_segment_avoiding_segment_union {U S : Set (ℝ × ℝ)}
    {r : ℝ × ℝ} (hU : IsOpen U) (hr : r ∈ U) (hS : S.Finite) (hrS : r ∉ S)
    (L : Finset ((ℝ × ℝ) × (ℝ × ℝ)))
    (hrL : r ∈ ⋃ p ∈ L, segment ℝ p.1 p.2) :
    ∃ q : ℝ × ℝ, q ≠ r ∧ segment ℝ r q ⊆ U \ S ∧
      segment ℝ r q ∩ (⋃ p ∈ L, segment ℝ p.1 p.2) = {r} := by
  classical
  let bad : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
    {p | p ∈ L ∧ r ∉ segment ℝ p.1 p.2}
  let A : Set (ℝ × ℝ) := ⋃ p ∈ bad, segment ℝ p.1 p.2
  have hbad : bad.Finite := L.finite_toSet.subset (by intro p hp; exact hp.1)
  have hA : IsClosed A := hbad.isClosed_biUnion fun p _ =>
    (LatticeProb.Topology.isCompact_segment p.1 p.2).isClosed
  have hrA : r ∉ A := by
    intro h
    obtain ⟨p, hp, hpseg⟩ := mem_iUnion₂.mp h
    exact hp.2 hpseg
  let ends : Set (ℝ × ℝ) := (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1) '' (↑L : Set ((ℝ × ℝ) × (ℝ × ℝ))) ∪
    (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.2) '' (↑L : Set ((ℝ × ℝ) × (ℝ × ℝ)))
  have hends : ends.Finite := (L.finite_toSet.image _).union (L.finite_toSet.image _)
  have hlocal : (⋃ p ∈ L, segment ℝ p.1 p.2) ∩ Aᶜ ⊆
      ⋃ v ∈ ends, segment ℝ r v := by
    rintro x ⟨hx, hxA⟩
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hx
    have hrp : r ∈ segment ℝ p.1 p.2 := by
      by_contra hnot
      exact hxA (mem_iUnion₂.mpr ⟨p, ⟨hp, hnot⟩, hxp⟩)
    rcases segment_subset_segments_at hrp hxp with h | h
    · exact mem_iUnion₂.mpr ⟨p.1, Or.inl ⟨p, hp, rfl⟩, h⟩
    · exact mem_iUnion₂.mpr ⟨p.2, Or.inr ⟨p, hp, rfl⟩, h⟩
  exact exists_segment_avoiding_locally_radial (hU.sdiff hS.isClosed) hA.isOpen_compl
    ⟨hr, hrS⟩ hrA hrL hends hlocal
end FiniteAvalanches.Electrical.StatementGeometry

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb

private theorem polygonal_chain_eq_segment_union : ∀ (vs : List (ℝ × ℝ)),
    ∃ L : Finset ((ℝ × ℝ) × (ℝ × ℝ)),
      LatticeProb.Topology.polygonalChain vs = ⋃ p ∈ L, segment ℝ p.1 p.2
  | [] => ⟨∅, by simp⟩
  | [a] => ⟨{(a, a)}, by simp [segment_same]⟩
  | a :: b :: rest => by
    obtain ⟨L, hL⟩ := polygonal_chain_eq_segment_union (b :: rest)
    refine ⟨insert (a, b) L, ?_⟩
    rw [LatticeProb.Topology.polygonal_chain_cons_cons, hL]
    ext x
    simp only [mem_union, mem_iUnion, Finset.mem_insert]
    aesop

/-- A finite collection of polygonal chains can be represented by finitely many segments. -/
theorem finite_polygonal_chains_eq_segment_union {ι : Type*} (s : Finset ι)
    (vs : ι → List (ℝ × ℝ)) : ∃ L : Finset ((ℝ × ℝ) × (ℝ × ℝ)),
      (⋃ i ∈ s, LatticeProb.Topology.polygonalChain (vs i)) =
        ⋃ p ∈ L, segment ℝ p.1 p.2 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨L, hL⟩ := ih
    obtain ⟨M, hM⟩ := polygonal_chain_eq_segment_union (vs i)
    refine ⟨M ∪ L, ?_⟩
    ext x
    simp only [mem_iUnion, Finset.mem_insert, Finset.mem_union]
    have hxM : x ∈ LatticeProb.Topology.polygonalChain (vs i) ↔
        ∃ p ∈ M, x ∈ segment ℝ p.1 p.2 := by simpa only [mem_iUnion, exists_prop] using Set.ext_iff.mp hM x
    have hxL : (∃ j ∈ s, x ∈ LatticeProb.Topology.polygonalChain (vs j)) ↔
        ∃ p ∈ L, x ∈ segment ℝ p.1 p.2 := by simpa only [mem_iUnion, exists_prop] using Set.ext_iff.mp hL x
    aesop
end FiniteAvalanches.Electrical.StatementGeometry

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb

/-- A finite union of polygonal chains has an escaping segment at each of its
points, avoiding any prescribed finite set disjoint from that point. -/
theorem exists_segment_avoiding_polygonal_chains {ι : Type*} {U S : Set (ℝ × ℝ)}
    {r : ℝ × ℝ} (hU : IsOpen U) (hr : r ∈ U) (hS : S.Finite) (hrS : r ∉ S)
    (s : Finset ι) (vs : ι → List (ℝ × ℝ))
    (hrvs : r ∈ ⋃ i ∈ s, LatticeProb.Topology.polygonalChain (vs i)) :
    ∃ q : ℝ × ℝ, q ≠ r ∧ segment ℝ r q ⊆ U \ S ∧
      segment ℝ r q ∩ (⋃ i ∈ s, LatticeProb.Topology.polygonalChain (vs i)) = {r} := by
  obtain ⟨L, hL⟩ := finite_polygonal_chains_eq_segment_union s vs
  rw [hL] at hrvs ⊢
  exact exists_segment_avoiding_segment_union hU hr hS hrS L hrvs

end FiniteAvalanches.Electrical.StatementGeometry

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb

private theorem exists_segment_first_contact {A : Set (ℝ × ℝ)} (hA : IsClosed A)
    {a b : ℝ × ℝ} (ha : a ∉ A) (hb : b ∈ A) :
    ∃ z ∈ A, segment ℝ a z ⊆ segment ℝ a b ∧ segment ℝ a z ∩ A = {z} := by
  let B := A ∩ segment ℝ b a
  have hB : IsCompact B := (LatticeProb.Topology.isCompact_segment b a).inter_left hA
  have hbB : b ∈ B := ⟨hb, left_mem_segment ℝ b a⟩
  have haB : a ∉ B := fun haB => ha haB.1
  obtain ⟨z, hz, hzseg, _, hsub, hmeet, _⟩ :=
    LatticeProb.Topology.exists_last_contact_segment hB hbB haB
  refine ⟨z, hz.1, ?_, ?_⟩
  · simpa only [segment_symm] using hsub
  · apply subset_antisymm
    · rintro x ⟨hxa, hxA⟩
      have hxseg : x ∈ segment ℝ z a := by simpa only [segment_symm] using hxa
      have hxB : x ∈ B := ⟨hxA, hsub hxseg⟩
      rw [← hmeet]
      exact ⟨hxseg, hxB⟩
    · exact singleton_subset_iff.mpr ⟨right_mem_segment ℝ a z, hz.1⟩

private theorem polygonal_chain_cons' (a : ℝ × ℝ) {vs : List (ℝ × ℝ)} (hv : vs ≠ []) :
    LatticeProb.Topology.polygonalChain (a :: vs) = segment ℝ a (vs.head hv) ∪
      LatticeProb.Topology.polygonalChain vs := by
  cases vs with
  | nil => exact (hv rfl).elim
  | cons v rest => rfl

/-- A finite polygonal chain can be truncated at its first contact with a closed set. -/
theorem exists_polygonal_chain_first_contact {A : Set (ℝ × ℝ)} (hA : IsClosed A) :
    ∀ (vs : List (ℝ × ℝ)) (hv : vs ≠ []), vs.head hv ∉ A →
      (LatticeProb.Topology.polygonalChain vs ∩ A).Nonempty →
      ∃ us : List (ℝ × ℝ), ∃ hu : us ≠ [], us.head hu = vs.head hv ∧
        us.getLast hu ∈ A ∧
        LatticeProb.Topology.polygonalChain us ⊆ LatticeProb.Topology.polygonalChain vs ∧
        LatticeProb.Topology.polygonalChain us ∩ A = {us.getLast hu}
  | [], hv, _, _ => (hv rfl).elim
  | [a], _, ha, ⟨z, hz, hzA⟩ => by
      have : z = a := hz
      exact (ha (this ▸ hzA)).elim
  | a :: b :: rest, _, ha, hnon => by
      by_cases hfirst : (segment ℝ a b ∩ A).Nonempty
      · obtain ⟨v, hvseg, hvA⟩ := hfirst
        obtain ⟨z, hzA, hzsub, hzinter⟩ := exists_segment_first_contact hA ha hvA
        have hseg : segment ℝ a z ⊆ segment ℝ a b :=
          hzsub.trans ((convex_segment a b).segment_subset (left_mem_segment ℝ a b) hvseg)
        refine ⟨[a, z], by simp, rfl, hzA, ?_, ?_⟩
        · change segment ℝ a z ∪ {z} ⊆ segment ℝ a b ∪ _
          exact union_subset (hseg.trans subset_union_left)
            (singleton_subset_iff.mpr (Or.inl (hseg (right_mem_segment ℝ a z))))
        · change (segment ℝ a z ∪ {z}) ∩ A = {z}
          rw [union_eq_left.mpr (singleton_subset_iff.mpr (right_mem_segment ℝ a z))]
          exact hzinter
      · have hb : b ∉ A := by
          intro hbA
          exact hfirst ⟨b, right_mem_segment ℝ a b, hbA⟩
        have htail : (LatticeProb.Topology.polygonalChain (b :: rest) ∩ A).Nonempty := by
          obtain ⟨z, hz, hzA⟩ := hnon
          rcases hz with hz | hz
          · exact (hfirst ⟨z, hz, hzA⟩).elim
          · exact ⟨z, hz, hzA⟩
        obtain ⟨us, hu, hhead, hlast, hsub, hinter⟩ :=
          exists_polygonal_chain_first_contact hA (b :: rest) (by simp) hb htail
        have hhead' : us.head hu = b := hhead
        have hnew : LatticeProb.Topology.polygonalChain (a :: us) =
            segment ℝ a b ∪ LatticeProb.Topology.polygonalChain us := by
          rw [polygonal_chain_cons' a hu, hhead']
        refine ⟨a :: us, by simp, rfl, ?_, ?_, ?_⟩
        · simpa only [List.getLast_cons hu] using hlast
        · rw [hnew]
          exact union_subset_union subset_rfl hsub
        · rw [hnew, List.getLast_cons hu, union_inter_distrib_right, hinter]
          have hempty : segment ℝ a b ∩ A = ∅ := Set.not_nonempty_iff_eq_empty.mp hfirst
          rw [hempty, empty_union]
end FiniteAvalanches.Electrical.StatementGeometry

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb

/-- A polygonal arc tree can be extended by an internally disjoint polygonal arc. -/
theorem exists_polygonal_path_to_polygonal_tree {ι : Type*} {U K S : Set (ℝ × ℝ)}
    {r x : ℝ × ℝ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hK : IsFiniteArcTree r K) (hKU : K ⊆ U) (hS : S.Finite) (hrS : r ∉ S)
    (s : Finset ι) (vs : ι → List (ℝ × ℝ))
    (hpoly : K = ⋃ i ∈ s, LatticeProb.Topology.polygonalChain (vs i))
    (hx : x ∈ (U \ K) \ S) :
    ∃ ws : List (ℝ × ℝ), ∃ hw : ws ≠ [],
      LatticeProb.Topology.IsSimplePolygonalChain ws ∧
      ws.head hw = x ∧ ws.getLast hw = r ∧
      LatticeProb.Topology.polygonalChain ws ⊆ U \ S ∧
      LatticeProb.Topology.polygonalChain ws ∩ K = {r} := by
  have hrK : r ∈ K := by
    clear hKU hpoly hx
    induction hK with
    | singleton => exact mem_singleton r
    | attach _ _ _ _ ih => exact Or.inr ih
  have hrU : r ∈ U := hKU hrK
  have hxr : x ≠ r := fun h => hx.1.2 (h ▸ hrK)
  have hS' : (S ∪ {x}).Finite := hS.union (finite_singleton x)
  have hrS' : r ∉ S ∪ {x} := by
    simp only [mem_union, mem_singleton_iff, not_or]
    exact ⟨hrS, Ne.symm hxr⟩
  obtain ⟨q, hqr, hqseg, hqmeet⟩ :=
    exists_segment_avoiding_polygonal_chains hU hrU hS' hrS' s vs (hpoly ▸ hrK)
  rw [← hpoly] at hqmeet
  have hqK : q ∉ K := by
    intro hqK
    have h : q ∈ segment ℝ r q ∩ K := ⟨right_mem_segment ℝ r q, hqK⟩
    rw [hqmeet, mem_singleton_iff] at h
    exact hqr h
  have hxseg : x ∉ segment ℝ r q := by
    intro hxseg
    exact (hqseg hxseg).2 (Or.inr (mem_singleton x))
  have hq : q ∈ ((U \ K) \ S) := by
    have h := hqseg (right_mem_segment ℝ r q)
    exact ⟨⟨h.1, hqK⟩, fun hqS => h.2 (Or.inl hqS)⟩
  have hopen : IsOpen (U \ K) := hU.sdiff hK.isCompact.isClosed
  have hconnected : IsPreconnected (U \ K) :=
    isPreconnected_sdiff_nonseparating_compact hU hconn hK.isCompact hK.not_separates hKU
  obtain ⟨as, ha, hasub, hahead, halast⟩ :=
    LatticeProb.Topology.exists_polygonal_chain_of_isPreconnected
      (hopen.sdiff hS.isClosed) (isPreconnected_sdiff_finite hopen hconnected hS) hx hq
  have hhit : (LatticeProb.Topology.polygonalChain as ∩ segment ℝ r q).Nonempty := by
    refine ⟨q, ?_, right_mem_segment ℝ r q⟩
    rw [← halast]
    exact LatticeProb.Topology.getLast_mem_polygonal_chain ha
  obtain ⟨bs, hb, hbhead, hbend, hbsub, _⟩ :=
    exists_polygonal_chain_first_contact (LatticeProb.Topology.isCompact_segment r q).isClosed
      as ha (by simpa only [hahead] using hxseg) hhit
  let cs := bs ++ [r]
  have hc : cs ≠ [] := List.append_ne_nil_of_left_ne_nil hb [r]
  have hchead : cs.head hc = x := by simpa only [cs, List.head_append_of_ne_nil hb, hbhead] using hahead
  have hclast : cs.getLast hc = r := List.getLast_append_singleton _
  have hcsub : LatticeProb.Topology.polygonalChain cs ⊆
      LatticeProb.Topology.polygonalChain as ∪ segment ℝ r q := by
    rw [show cs = bs ++ [r] from rfl, LatticeProb.Topology.polygonal_chain_concat hb]
    apply union_subset_union hbsub
    exact (convex_segment r q).segment_subset hbend (left_mem_segment ℝ r q)
  have hcU : LatticeProb.Topology.polygonalChain cs ⊆ U \ S := by
    apply hcsub.trans
    apply union_subset
    · exact fun y hy => ⟨(hasub hy).1.1, (hasub hy).2⟩
    · exact fun y hy => ⟨(hqseg hy).1, fun hyS => (hqseg hy).2 (Or.inl hyS)⟩
  have hcK : LatticeProb.Topology.polygonalChain cs ∩ K = {r} := by
    apply subset_antisymm
    · rintro y ⟨hy, hyK⟩
      rcases hcsub hy with hy | hy
      · exact ((hasub hy).1.2 hyK).elim
      · rw [← hqmeet]
        exact ⟨hy, hyK⟩
    · apply singleton_subset_iff.mpr
      rw [← hclast]
      exact ⟨LatticeProb.Topology.getLast_mem_polygonal_chain hc, hclast.symm ▸ hrK⟩
  have hcne : cs.head hc ≠ cs.getLast hc := by rw [hchead, hclast]; exact hxr
  obtain ⟨ws, hw, hsimple, hhead, hlast, hsub, _, _⟩ :=
    LatticeProb.Topology.exists_injective_polygonal_arc cs hc hcne
  refine ⟨ws, hw, hsimple, hhead.trans hchead, hlast.trans hclast, hsub.trans hcU, ?_⟩
  apply subset_antisymm
  · exact (inter_subset_inter_left K hsub).trans hcK.le
  · apply singleton_subset_iff.mpr
    refine ⟨?_, hrK⟩
    rw [← (hlast.trans hclast)]
    exact LatticeProb.Topology.getLast_mem_polygonal_chain hw
end FiniteAvalanches.Electrical.StatementGeometry

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb
/-- Simple polygonal chains with pairwise intersections at their common root
form a finite arc tree. -/
theorem isFiniteArcTree_finset_polygonal_chains {ι : Type*} (s : Finset ι)
    {r : ℝ × ℝ} {x : ι → ℝ × ℝ} (vs : ι → List (ℝ × ℝ))
    (hs : ∀ i ∈ s, LatticeProb.Topology.IsSimplePolygonalChain (vs i))
    (hh : ∀ i (hi : i ∈ s), (vs i).head (hs i hi).ne_nil = x i)
    (hl : ∀ i (hi : i ∈ s), (vs i).getLast (hs i hi).ne_nil = r)
    (hne : ∀ i ∈ s, x i ≠ r)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      LatticeProb.Topology.polygonalChain (vs i) ∩
        LatticeProb.Topology.polygonalChain (vs j) = {r}) :
    IsFiniteArcTree r ({r} ∪ ⋃ i ∈ s, LatticeProb.Topology.polygonalChain (vs i)) := by
  classical
  let p : ∀ i, Path (x i) r := fun i =>
    if hi : i ∈ s then
      (LatticeProb.Topology.polygonalChainPath (vs i) (hs i hi).ne_nil).cast
        (hh i hi).symm (hl i hi).symm
    else Path.segment (x i) r
  have hp : ∀ i ∈ s, Function.Injective (p i) := by
    intro i hi
    dsimp only [p]
    rw [dif_pos hi]
    apply (hs i hi).path_injective
    rw [hh i hi, hl i hi]
    exact hne i hi
  have htrace : ∀ i ∈ s, range (p i) = LatticeProb.Topology.polygonalChain (vs i) := by
    intro i hi
    dsimp only [p]
    rw [dif_pos hi]
    exact LatticeProb.Topology.range_polygonal_chain_path _ _
  have ht := isFiniteArcTree_finset_paths s p hp (by
    intro i hi j hj hij
    rw [htrace i hi, htrace j hj]
    exact hd i hi j hj hij)
  convert ht using 1
  congr 1
  ext z
  simp only [mem_iUnion]
  constructor
  · rintro ⟨i, hi, hz⟩
    exact ⟨i, hi, by simpa only [htrace i hi] using hz⟩
  · rintro ⟨i, hi, hz⟩
    exact ⟨i, hi, by simpa only [htrace i hi] using hz⟩
end FiniteAvalanches.Electrical.StatementGeometry

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb
/-- A polygonal star, including its root, is a finite union of polygonal chains. -/
theorem finset_polygonal_star_representation {ι : Type*} (s : Finset ι)
    (r : ℝ × ℝ) (vs : ι → List (ℝ × ℝ)) :
    ∃ (t : Finset (Option ι)) (ws : Option ι → List (ℝ × ℝ)),
      {r} ∪ (⋃ i ∈ s, LatticeProb.Topology.polygonalChain (vs i)) =
      ⋃ j ∈ t, LatticeProb.Topology.polygonalChain (ws j) := by
  classical
  let ws : Option ι → List (ℝ × ℝ) := fun i =>
    match i with | none => [r] | some i => vs i
  refine ⟨insert none (s.image some), ws, ?_⟩
  ext z
  simp only [mem_union, mem_singleton_iff, mem_iUnion, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (hz | ⟨i, hi, hz⟩)
    · exact ⟨none, Or.inl rfl, by simpa [ws] using hz⟩
    · exact ⟨some i, Or.inr ⟨i, hi, rfl⟩, hz⟩
  · rintro ⟨j, hj, hz⟩
    rcases hj with h | ⟨i, hi, rfl⟩
    · subst j
      left
      simpa [ws] using hz
    · exact Or.inr ⟨i, hi, hz⟩
end FiniteAvalanches.Electrical.StatementGeometry

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb

/-- Finitely many distinct points in an open connected plane region can be joined
 to a common root by polygonal arcs meeting only at the root, while avoiding
 a prescribed finite set. -/
theorem exists_disjoint_polygonal_star {ι : Type*} {U S : Set (ℝ × ℝ)}
    {r : ℝ × ℝ} {x : ι → ℝ × ℝ} (hU : IsOpen U)
    (hconn : IsPreconnected U) (s : Finset ι) (hS : S.Finite)
    (hr : r ∈ U \ S) (hx : ∀ i ∈ s, x i ∈ U \ S)
    (hxr : ∀ i ∈ s, x i ≠ r)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → x i ≠ x j) :
    ∃ (vs : ι → List (ℝ × ℝ))
      (hs : ∀ i ∈ s, LatticeProb.Topology.IsSimplePolygonalChain (vs i)),
      (∀ i (hi : i ∈ s), (vs i).head (hs i hi).ne_nil = x i) ∧
      (∀ i (hi : i ∈ s), (vs i).getLast (hs i hi).ne_nil = r) ∧
      (∀ i ∈ s, LatticeProb.Topology.polygonalChain (vs i) ⊆ U \ S) ∧
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        LatticeProb.Topology.polygonalChain (vs i) ∩
          LatticeProb.Topology.polygonalChain (vs j) = {r}) := by
  classical
  induction s using Finset.induction_on generalizing S with
  | empty =>
      refine ⟨fun _ => [], ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  | @insert i s hi ih =>
      have hxi := hx i (Finset.mem_insert_self i s)
      have hri := hxr i (Finset.mem_insert_self i s)
      have hS' : (S ∪ {x i}).Finite := hS.union (finite_singleton _)
      have hr' : r ∈ U \ (S ∪ {x i}) := by
        simp only [mem_sdiff, mem_union, mem_singleton_iff, not_or]
        exact ⟨hr.1, hr.2, Ne.symm hri⟩
      have hx' : ∀ j ∈ s, x j ∈ U \ (S ∪ {x i}) := by
        intro j hj
        have hj' := hx j (Finset.mem_insert_of_mem hj)
        simp only [mem_sdiff, mem_union, mem_singleton_iff, not_or]
        exact ⟨hj'.1, hj'.2, hinj j (Finset.mem_insert_of_mem hj) i
          (Finset.mem_insert_self i s) (fun h => hi (h ▸ hj))⟩
      obtain ⟨vs, hs, hh, hl, hsub, hd⟩ := ih hS' hr' hx'
        (fun j hj => hxr j (Finset.mem_insert_of_mem hj))
        (fun j hj k hk => hinj j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
      let K := {r} ∪ ⋃ j ∈ s, LatticeProb.Topology.polygonalChain (vs j)
      have htree : IsFiniteArcTree r K :=
        isFiniteArcTree_finset_polygonal_chains s vs hs hh hl
          (fun j hj => hxr j (Finset.mem_insert_of_mem hj)) hd
      have hKU : K ⊆ U := by
        refine union_subset (singleton_subset_iff.mpr hr.1) (iUnion₂_subset ?_)
        intro j hj z hz
        exact (hsub j hj hz).1
      have hxiK : x i ∉ K := by
        intro h
        rcases h with h | h
        · exact hri (mem_singleton_iff.mp h)
        · obtain ⟨j, hj, hz⟩ := mem_iUnion₂.mp h
          exact (hsub j hj hz).2 (Or.inr (mem_singleton _))
      obtain ⟨t, ws, hpoly⟩ := finset_polygonal_star_representation s r vs
      obtain ⟨v, hv, hsimple, hhead, hlast, hvsub, hvmeet⟩ :=
        exists_polygonal_path_to_polygonal_tree hU hconn htree hKU hS hr.2 t ws hpoly
          ⟨⟨hxi.1, hxiK⟩, hxi.2⟩
      let vs' := Function.update vs i v
      have hmeet : ∀ j ∈ s, LatticeProb.Topology.polygonalChain v ∩
          LatticeProb.Topology.polygonalChain (vs j) = {r} := by
        intro j hj
        apply subset_antisymm
        · intro z hz
          apply hvmeet.le
          exact ⟨hz.1, Or.inr (mem_iUnion₂.mpr ⟨j, hj, hz.2⟩)⟩
        · apply singleton_subset_iff.mpr
          refine ⟨?_, ?_⟩
          · rw [← hlast]; exact LatticeProb.Topology.getLast_mem_polygonal_chain hv
          · rw [← hl j hj]; exact LatticeProb.Topology.getLast_mem_polygonal_chain (hs j hj).ne_nil
      have hs' : ∀ j ∈ insert i s, LatticeProb.Topology.IsSimplePolygonalChain (vs' j) := by
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa [vs'] using hsimple
        · simpa [vs', Function.update_of_ne (show j ≠ i from fun h => hi (h ▸ hj))] using hs j hj
      refine ⟨vs', hs', ?_, ?_, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa [vs'] using hhead
        · simpa [vs', Function.update_of_ne (show j ≠ i from fun h => hi (h ▸ hj))] using hh j hj
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa [vs'] using hlast
        · simpa [vs', Function.update_of_ne (show j ≠ i from fun h => hi (h ▸ hj))] using hl j hj
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa [vs'] using hvsub
        · have h := hsub j hj
          simp only [vs', Function.update_of_ne (show j ≠ i from fun h => hi (h ▸ hj))]
          exact fun z hz => ⟨(h hz).1, fun hzS => (h hz).2 (Or.inl hzS)⟩
      · intro j hj k hk hjk
        by_cases hji : j = i
        · subst j
          have hk' : k ∈ s := (Finset.mem_insert.mp hk).resolve_left (Ne.symm hjk)
          have hkne : k ≠ i := fun h => hi (h ▸ hk')
          simpa [vs', Function.update_of_ne hkne] using hmeet k hk'
        · have hj' : j ∈ s := (Finset.mem_insert.mp hj).resolve_left hji
          by_cases hki : k = i
          · subst k
            simpa [vs', Function.update_of_ne hji, inter_comm] using hmeet j hj'
          · have hk' : k ∈ s := (Finset.mem_insert.mp hk).resolve_left hki
            simpa [vs', Function.update_of_ne hji, Function.update_of_ne hki] using
              hd j hj' k hk' hjk

end FiniteAvalanches.Electrical.StatementGeometry

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb

/-- Finitely many distinct points can be joined to a common root by injective
paths that meet pairwise only at the root and avoid a finite set. -/
theorem exists_disjoint_path_star {ι : Type*} {U S : Set (ℝ × ℝ)}
    {r : ℝ × ℝ} {x : ι → ℝ × ℝ} (hU : IsOpen U)
    (hconn : IsPreconnected U) (s : Finset ι) (hS : S.Finite)
    (hr : r ∈ U \ S) (hx : ∀ i ∈ s, x i ∈ U \ S)
    (hxr : ∀ i ∈ s, x i ≠ r)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → x i ≠ x j) :
    ∃ p : ∀ i, Path (x i) r,
      (∀ i ∈ s, Function.Injective (p i)) ∧
      (∀ i ∈ s, range (p i) ⊆ U \ S) ∧
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → range (p i) ∩ range (p j) = {r}) := by
  classical
  obtain ⟨vs, hs, hh, hl, hsub, hd⟩ :=
    exists_disjoint_polygonal_star hU hconn s hS hr hx hxr hinj
  let p : ∀ i, Path (x i) r := fun i =>
    if hi : i ∈ s then
      (LatticeProb.Topology.polygonalChainPath (vs i) (hs i hi).ne_nil).cast
        (hh i hi).symm (hl i hi).symm
    else Path.segment (x i) r
  have hp : ∀ i ∈ s, Function.Injective (p i) := by
    intro i hi
    dsimp only [p]
    rw [dif_pos hi]
    apply (hs i hi).path_injective
    rw [hh i hi, hl i hi]
    exact hxr i hi
  have htrace : ∀ i ∈ s, range (p i) = LatticeProb.Topology.polygonalChain (vs i) := by
    intro i hi
    dsimp only [p]
    rw [dif_pos hi]
    exact LatticeProb.Topology.range_polygonal_chain_path _ _
  refine ⟨p, hp, ?_, ?_⟩
  · intro i hi
    rw [htrace i hi]
    exact hsub i hi
  · intro i hi j hj hij
    rw [htrace i hi, htrace j hj]
    exact hd i hi j hj hij

end FiniteAvalanches.Electrical.StatementGeometry

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb

open Source BSST

/-- Distinct marked points in each face admit a star of injective paths avoiding
prescribed disjoint arcs and finitely many points. Stars in different faces are disjoint. -/
theorem exists_face_disjoint_path_stars_avoiding_paths
    {V E : Type} {ι κ : Type*} [Fintype V] [Fintype E] {J : CopiedGraph V E}
    (D : Drawing J) (s : Face D → Finset ι)
    {a b : ι → ℝ × ℝ} (obstacle : ∀ i, Path (a i) (b i))
    (hobs : ∀ F i, i ∈ s F → Function.Injective (obstacle i))
    (hdisj : ∀ F i, i ∈ s F → ∀ j, j ∈ s F → i ≠ j →
      Disjoint (range (obstacle i)) (range (obstacle j)))
    (hobsF : ∀ F i, i ∈ s F → range (obstacle i) ⊆ faceRegion D F)
    (T : Face D → Set (ℝ × ℝ)) (hT : ∀ F, (T F).Finite)
    (u : Face D → Finset κ) (x : κ → ℝ × ℝ) (r : Face D → ℝ × ℝ)
    (hr : ∀ F, r F ∈ (faceRegion D F \ (⋃ i ∈ s F, range (obstacle i))) \ T F)
    (hx : ∀ F j, j ∈ u F →
      x j ∈ (faceRegion D F \ (⋃ i ∈ s F, range (obstacle i))) \ T F)
    (hxr : ∀ F j, j ∈ u F → x j ≠ r F)
    (hinj : ∀ F j, j ∈ u F → ∀ k, k ∈ u F → j ≠ k → x j ≠ x k) :
    ∃ p : ∀ F j, Path (x j) (r F),
      (∀ F j, j ∈ u F → Function.Injective (p F j)) ∧
      (∀ F j, j ∈ u F → range (p F j) ⊆
        (faceRegion D F \ (⋃ i ∈ s F, range (obstacle i))) \ T F) ∧
      (∀ F j, j ∈ u F → ∀ k, k ∈ u F → j ≠ k →
        range (p F j) ∩ range (p F k) = {r F}) ∧
      (∀ F G, F ≠ G → ∀ j ∈ u F, ∀ k ∈ u G,
        Disjoint (range (p F j)) (range (p G k))) := by
  have hex : ∀ F, ∃ p : ∀ j, Path (x j) (r F),
      (∀ j ∈ u F, Function.Injective (p j)) ∧
      (∀ j ∈ u F, range (p j) ⊆
        (faceRegion D F \ (⋃ i ∈ s F, range (obstacle i))) \ T F) ∧
      (∀ j ∈ u F, ∀ k ∈ u F, j ≠ k → range (p j) ∩ range (p k) = {r F}) := by
    intro F
    have hc : IsCompact (⋃ i ∈ s F, range (obstacle i)) :=
      (s F).isCompact_biUnion (fun i _ => isCompact_range (obstacle i).continuous)
    exact exists_disjoint_path_star ((punctured_faceRegion_isOpen D F).sdiff hc.isClosed)
      (isPreconnected_sdiff_finset_paths (punctured_faceRegion_isOpen D F)
        (faceRegion_isConnected D F).isPreconnected (s F) obstacle (hobs F) (hdisj F)
        (hobsF F)) (u F) (hT F) (hr F) (hx F) (hxr F) (hinj F)
  choose p hp hsub hpair using hex
  refine ⟨p, hp, hsub, hpair, ?_⟩
  intro F G hFG j hj k hk
  exact (faceRegion_disjoint D hFG).mono
    (fun z hz => ((hsub F j hj hz).1).1)
    (fun z hz => ((hsub G k hk hz).1).1)


/-- Face points admit disjoint stars avoiding finitely many arcs that are disjoint
inside each face and meet its complement in a preconnected set. -/
theorem exists_face_disjoint_path_stars_avoiding_paths_disjoint_inside
    {V E : Type} {ι κ : Type*} [Fintype V] [Fintype E] {J : CopiedGraph V E}
    (D : Drawing J) (s : Face D → Finset ι)
    {a b : ι → ℝ × ℝ} (obstacle : ∀ i, Path (a i) (b i))
    (hobs : ∀ F i, i ∈ s F → Function.Injective (obstacle i))
    (hdisj : ∀ F i, i ∈ s F → ∀ j, j ∈ s F → i ≠ j →
      Disjoint (range (obstacle i) ∩ faceRegion D F) (range (obstacle j)))
    (hobsF : ∀ F i, i ∈ s F →
      IsPreconnected (range (obstacle i) ∩ (faceRegion D F)ᶜ))
    (T : Face D → Set (ℝ × ℝ)) (hT : ∀ F, (T F).Finite)
    (u : Face D → Finset κ) (x : κ → ℝ × ℝ) (r : Face D → ℝ × ℝ)
    (hr : ∀ F, r F ∈ (faceRegion D F \ (⋃ i ∈ s F, range (obstacle i))) \ T F)
    (hx : ∀ F j, j ∈ u F →
      x j ∈ (faceRegion D F \ (⋃ i ∈ s F, range (obstacle i))) \ T F)
    (hxr : ∀ F j, j ∈ u F → x j ≠ r F)
    (hinj : ∀ F j, j ∈ u F → ∀ k, k ∈ u F → j ≠ k → x j ≠ x k) :
    ∃ p : ∀ F j, Path (x j) (r F),
      (∀ F j, j ∈ u F → Function.Injective (p F j)) ∧
      (∀ F j, j ∈ u F → range (p F j) ⊆
        (faceRegion D F \ (⋃ i ∈ s F, range (obstacle i))) \ T F) ∧
      (∀ F j, j ∈ u F → ∀ k, k ∈ u F → j ≠ k →
        range (p F j) ∩ range (p F k) = {r F}) ∧
      (∀ F G, F ≠ G → ∀ j ∈ u F, ∀ k ∈ u G,
        Disjoint (range (p F j)) (range (p G k))) := by
  have hex : ∀ F, ∃ p : ∀ j, Path (x j) (r F),
      (∀ j ∈ u F, Function.Injective (p j)) ∧
      (∀ j ∈ u F, range (p j) ⊆
        (faceRegion D F \ (⋃ i ∈ s F, range (obstacle i))) \ T F) ∧
      (∀ j ∈ u F, ∀ k ∈ u F, j ≠ k → range (p j) ∩ range (p k) = {r F}) := by
    intro F
    have hc : IsCompact (⋃ i ∈ s F, range (obstacle i)) :=
      (s F).isCompact_biUnion (fun i _ => isCompact_range (obstacle i).continuous)
    exact exists_disjoint_path_star ((punctured_faceRegion_isOpen D F).sdiff hc.isClosed)
      (isPreconnected_sdiff_finset_paths_of_disjoint_inside (punctured_faceRegion_isOpen D F)
        (faceRegion_isConnected D F).isPreconnected (s F) obstacle (hobs F) (hdisj F)
        (hobsF F)) (u F) (hT F) (hr F) (hx F) (hxr F) (hinj F)
  choose p hp hsub hpair using hex
  refine ⟨p, hp, hsub, hpair, ?_⟩
  intro F G hFG j hj k hk
  exact (faceRegion_disjoint D hFG).mono
    (fun z hz => ((hsub F j hj hz).1).1)
    (fun z hz => ((hsub G k hk hz).1).1)

/-- Face points admit disjoint stars avoiding finitely many disjoint arcs, including
arcs that meet the complement of their face in a preconnected set. -/
theorem exists_face_disjoint_path_stars_avoiding_boundary_paths
    {V E : Type} {ι κ : Type*} [Fintype V] [Fintype E] {J : CopiedGraph V E}
    (D : Drawing J) (s : Face D → Finset ι)
    {a b : ι → ℝ × ℝ} (obstacle : ∀ i, Path (a i) (b i))
    (hobs : ∀ F i, i ∈ s F → Function.Injective (obstacle i))
    (hdisj : ∀ F i, i ∈ s F → ∀ j, j ∈ s F → i ≠ j →
      Disjoint (range (obstacle i)) (range (obstacle j)))
    (hobsF : ∀ F i, i ∈ s F →
      IsPreconnected (range (obstacle i) ∩ (faceRegion D F)ᶜ))
    (T : Face D → Set (ℝ × ℝ)) (hT : ∀ F, (T F).Finite)
    (u : Face D → Finset κ) (x : κ → ℝ × ℝ) (r : Face D → ℝ × ℝ)
    (hr : ∀ F, r F ∈ (faceRegion D F \ (⋃ i ∈ s F, range (obstacle i))) \ T F)
    (hx : ∀ F j, j ∈ u F →
      x j ∈ (faceRegion D F \ (⋃ i ∈ s F, range (obstacle i))) \ T F)
    (hxr : ∀ F j, j ∈ u F → x j ≠ r F)
    (hinj : ∀ F j, j ∈ u F → ∀ k, k ∈ u F → j ≠ k → x j ≠ x k) :
    ∃ p : ∀ F j, Path (x j) (r F),
      (∀ F j, j ∈ u F → Function.Injective (p F j)) ∧
      (∀ F j, j ∈ u F → range (p F j) ⊆
        (faceRegion D F \ (⋃ i ∈ s F, range (obstacle i))) \ T F) ∧
      (∀ F j, j ∈ u F → ∀ k, k ∈ u F → j ≠ k →
        range (p F j) ∩ range (p F k) = {r F}) ∧
      (∀ F G, F ≠ G → ∀ j ∈ u F, ∀ k ∈ u G,
        Disjoint (range (p F j)) (range (p G k))) := by
  exact exists_face_disjoint_path_stars_avoiding_paths_disjoint_inside D s obstacle hobs
    (fun F i hi j hj hij => (hdisj F i hi j hj hij).mono_left inter_subset_left)
    hobsF T hT u x r hr hx hxr hinj


end FiniteAvalanches.Electrical.StatementGeometry

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb

open Source BSST

/-- Nonempty finite marked sets in faces admit roots and disjoint path stars
avoiding prescribed disjoint arcs and finitely many points. -/
theorem exists_rooted_face_disjoint_path_stars_avoiding_paths
    {V E : Type} {ι : Type*} [Fintype V] [Fintype E] {J : CopiedGraph V E}
    (D : Drawing J) (s : Face D → Finset ι)
    {a b : ι → ℝ × ℝ} (obstacle : ∀ i, Path (a i) (b i))
    (hobs : ∀ F i, i ∈ s F → Function.Injective (obstacle i))
    (hdisj : ∀ F i, i ∈ s F → ∀ j, j ∈ s F → i ≠ j →
      Disjoint (range (obstacle i)) (range (obstacle j)))
    (hobsF : ∀ F i, i ∈ s F → range (obstacle i) ⊆ faceRegion D F)
    (T : Face D → Set (ℝ × ℝ)) (hT : ∀ F, (T F).Finite)
    (A : Face D → Finset (ℝ × ℝ)) (hne : ∀ F, (A F).Nonempty)
    (hA : ∀ F z, z ∈ A F →
      z ∈ (faceRegion D F \ (⋃ i ∈ s F, range (obstacle i))) \ T F) :
    ∃ (r : Face D → ℝ × ℝ) (p : ∀ F z, Path z (r F)),
      (∀ F, r F ∈ (faceRegion D F \ (⋃ i ∈ s F, range (obstacle i))) \ T F ∧
        r F ∉ A F) ∧
      (∀ F z, z ∈ A F → Function.Injective (p F z)) ∧
      (∀ F z, z ∈ A F → range (p F z) ⊆
        (faceRegion D F \ (⋃ i ∈ s F, range (obstacle i))) \ T F) ∧
      (∀ F z, z ∈ A F → ∀ w, w ∈ A F → z ≠ w →
        range (p F z) ∩ range (p F w) = {r F}) ∧
      (∀ F G, F ≠ G → ∀ z ∈ A F, ∀ w ∈ A G,
        Disjoint (range (p F z)) (range (p G w))) := by
  have hroot : ∀ F, ∃ r : ℝ × ℝ,
      r ∈ (faceRegion D F \ (⋃ i ∈ s F, range (obstacle i))) \ T F ∧ r ∉ A F := by
    intro F
    have hc : IsCompact (⋃ i ∈ s F, range (obstacle i)) :=
      (s F).isCompact_biUnion (fun i _ => isCompact_range (obstacle i).continuous)
    have hopen : IsOpen (faceRegion D F \ (⋃ i ∈ s F, range (obstacle i))) :=
      (punctured_faceRegion_isOpen D F).sdiff hc.isClosed
    obtain ⟨z, hz⟩ := hne F
    have hnonempty : (faceRegion D F \ (⋃ i ∈ s F, range (obstacle i))).Nonempty :=
      ⟨z, (hA F z hz).1⟩
    have hfinite : (T F ∪ (A F : Set (ℝ × ℝ))).Finite :=
      (hT F).union (A F).finite_toSet
    have hdense : Dense (T F ∪ (A F : Set (ℝ × ℝ)))ᶜ := by
      rw [Set.compl_eq_univ_sdiff]
      exact dense_univ.sdiff_finite hfinite
    obtain ⟨r, hr, havoid⟩ := hdense.inter_open_nonempty _ hopen hnonempty
    exact ⟨r, ⟨hr, fun ht => havoid (Or.inl ht)⟩, fun ht => havoid (Or.inr ht)⟩
  choose r hr hrA using hroot
  obtain ⟨p, hp, hsub, hpair, hsep⟩ :=
    exists_face_disjoint_path_stars_avoiding_paths D s obstacle hobs hdisj hobsF T hT A id r
      hr hA (fun F z hz h => hrA F (h ▸ hz)) (fun _ _ _ _ _ h => h)
  exact ⟨r, p, fun F => ⟨hr F, hrA F⟩, hp, hsub, hpair, hsep⟩


/-- Nonempty finite marked sets in faces admit roots and disjoint stars avoiding
arcs disjoint inside the face that meet its complement in a preconnected set. -/
theorem exists_rooted_face_disjoint_path_stars_avoiding_paths_disjoint_inside
    {V E : Type} {ι : Type*} [Fintype V] [Fintype E] {J : CopiedGraph V E}
    (D : Drawing J) (s : Face D → Finset ι)
    {a b : ι → ℝ × ℝ} (obstacle : ∀ i, Path (a i) (b i))
    (hobs : ∀ F i, i ∈ s F → Function.Injective (obstacle i))
    (hdisj : ∀ F i, i ∈ s F → ∀ j, j ∈ s F → i ≠ j →
      Disjoint (range (obstacle i) ∩ faceRegion D F) (range (obstacle j)))
    (hobsF : ∀ F i, i ∈ s F →
      IsPreconnected (range (obstacle i) ∩ (faceRegion D F)ᶜ))
    (T : Face D → Set (ℝ × ℝ)) (hT : ∀ F, (T F).Finite)
    (A : Face D → Finset (ℝ × ℝ)) (hne : ∀ F, (A F).Nonempty)
    (hA : ∀ F z, z ∈ A F →
      z ∈ (faceRegion D F \ (⋃ i ∈ s F, range (obstacle i))) \ T F) :
    ∃ (r : Face D → ℝ × ℝ) (p : ∀ F z, Path z (r F)),
      (∀ F, r F ∈ (faceRegion D F \ (⋃ i ∈ s F, range (obstacle i))) \ T F ∧
        r F ∉ A F) ∧
      (∀ F z, z ∈ A F → Function.Injective (p F z)) ∧
      (∀ F z, z ∈ A F → range (p F z) ⊆
        (faceRegion D F \ (⋃ i ∈ s F, range (obstacle i))) \ T F) ∧
      (∀ F z, z ∈ A F → ∀ w, w ∈ A F → z ≠ w →
        range (p F z) ∩ range (p F w) = {r F}) ∧
      (∀ F G, F ≠ G → ∀ z ∈ A F, ∀ w ∈ A G,
        Disjoint (range (p F z)) (range (p G w))) := by
  have hroot : ∀ F, ∃ r : ℝ × ℝ,
      r ∈ (faceRegion D F \ (⋃ i ∈ s F, range (obstacle i))) \ T F ∧ r ∉ A F := by
    intro F
    have hc : IsCompact (⋃ i ∈ s F, range (obstacle i)) :=
      (s F).isCompact_biUnion (fun i _ => isCompact_range (obstacle i).continuous)
    have hopen : IsOpen (faceRegion D F \ (⋃ i ∈ s F, range (obstacle i))) :=
      (punctured_faceRegion_isOpen D F).sdiff hc.isClosed
    obtain ⟨z, hz⟩ := hne F
    have hnonempty : (faceRegion D F \ (⋃ i ∈ s F, range (obstacle i))).Nonempty :=
      ⟨z, (hA F z hz).1⟩
    have hfinite : (T F ∪ (A F : Set (ℝ × ℝ))).Finite :=
      (hT F).union (A F).finite_toSet
    have hdense : Dense (T F ∪ (A F : Set (ℝ × ℝ)))ᶜ := by
      rw [Set.compl_eq_univ_sdiff]
      exact dense_univ.sdiff_finite hfinite
    obtain ⟨r, hr, havoid⟩ := hdense.inter_open_nonempty _ hopen hnonempty
    exact ⟨r, ⟨hr, fun ht => havoid (Or.inl ht)⟩, fun ht => havoid (Or.inr ht)⟩
  choose r hr hrA using hroot
  obtain ⟨p, hp, hsub, hpair, hsep⟩ :=
    exists_face_disjoint_path_stars_avoiding_paths_disjoint_inside D s obstacle hobs hdisj hobsF T hT A id r
      hr hA (fun F z hz h => hrA F (h ▸ hz)) (fun _ _ _ _ _ h => h)
  exact ⟨r, p, fun F => ⟨hr F, hrA F⟩, hp, hsub, hpair, hsep⟩

/-- Nonempty finite marked sets in faces admit roots and disjoint stars avoiding
arcs that meet the complement of their face in a preconnected set. -/
theorem exists_rooted_face_disjoint_path_stars_avoiding_boundary_paths
    {V E : Type} {ι : Type*} [Fintype V] [Fintype E] {J : CopiedGraph V E}
    (D : Drawing J) (s : Face D → Finset ι)
    {a b : ι → ℝ × ℝ} (obstacle : ∀ i, Path (a i) (b i))
    (hobs : ∀ F i, i ∈ s F → Function.Injective (obstacle i))
    (hdisj : ∀ F i, i ∈ s F → ∀ j, j ∈ s F → i ≠ j →
      Disjoint (range (obstacle i)) (range (obstacle j)))
    (hobsF : ∀ F i, i ∈ s F →
      IsPreconnected (range (obstacle i) ∩ (faceRegion D F)ᶜ))
    (T : Face D → Set (ℝ × ℝ)) (hT : ∀ F, (T F).Finite)
    (A : Face D → Finset (ℝ × ℝ)) (hne : ∀ F, (A F).Nonempty)
    (hA : ∀ F z, z ∈ A F →
      z ∈ (faceRegion D F \ (⋃ i ∈ s F, range (obstacle i))) \ T F) :
    ∃ (r : Face D → ℝ × ℝ) (p : ∀ F z, Path z (r F)),
      (∀ F, r F ∈ (faceRegion D F \ (⋃ i ∈ s F, range (obstacle i))) \ T F ∧
        r F ∉ A F) ∧
      (∀ F z, z ∈ A F → Function.Injective (p F z)) ∧
      (∀ F z, z ∈ A F → range (p F z) ⊆
        (faceRegion D F \ (⋃ i ∈ s F, range (obstacle i))) \ T F) ∧
      (∀ F z, z ∈ A F → ∀ w, w ∈ A F → z ≠ w →
        range (p F z) ∩ range (p F w) = {r F}) ∧
      (∀ F G, F ≠ G → ∀ z ∈ A F, ∀ w ∈ A G,
        Disjoint (range (p F z)) (range (p G w))) := by
  exact exists_rooted_face_disjoint_path_stars_avoiding_paths_disjoint_inside D s obstacle hobs
    (fun F i hi j hj hij => (hdisj F i hi j hj hij).mono_left inter_subset_left)
    hobsF T hT A hne hA


end FiniteAvalanches.Electrical.StatementGeometry

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb

open QuantumZipper.CA.Topo MatedCRTHarmonic.Topology

/-- Adding pairwise disjoint arcs to a compact nonseparating set preserves
nonseparation when each arc meets the set in a preconnected set. -/
theorem not_separates_image_union_finset_paths {ι : Type*} {K : Set (ℝ × ℝ)}
    (hK : IsCompact K)
    (hsep : ∀ ⦃a b : ℂ⦄,
      a ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' K →
      b ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' K →
      ¬ Separates (Complex.equivRealProdCLM.symm.toHomeomorph '' K) a b)
    (s : Finset ι) {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (range (p i)) (range (p j)))
    (hmeet : ∀ i ∈ s, IsPreconnected (range (p i) ∩ K)) :
    ∀ ⦃a b : ℂ⦄,
      a ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' (K ∪ ⋃ i ∈ s, range (p i)) →
      b ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' (K ∪ ⋃ i ∈ s, range (p i)) →
      ¬ Separates (Complex.equivRealProdCLM.symm.toHomeomorph ''
        (K ∪ ⋃ i ∈ s, range (p i))) a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hsep
  | @insert i s hi ih =>
      have hc : IsCompact (K ∪ ⋃ j ∈ s, range (p j)) :=
        hK.union (s.isCompact_biUnion (fun j _ => isCompact_range (p j).continuous))
      have hinter : range (p i) ∩ (K ∪ ⋃ j ∈ s, range (p j)) = range (p i) ∩ K := by
        ext z
        constructor
        · rintro ⟨hzi, hzK | hzunion⟩
          · exact ⟨hzi, hzK⟩
          · obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp hzunion
            exact (Set.disjoint_left.mp (hd i (Finset.mem_insert_self i s) j
              (Finset.mem_insert_of_mem hj) (fun h => hi (h ▸ hj))) hzi hzj).elim
        · rintro ⟨hz, hzK⟩
          exact ⟨hz, Or.inl hzK⟩
      have hnew := not_separates_image_union_path hc
        (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))
          (fun j hj k hk => hd j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
          (fun j hj => hmeet j (Finset.mem_insert_of_mem hj)))
        (p i) (hp i (Finset.mem_insert_self i s)) (hinter ▸ hmeet i (Finset.mem_insert_self i s))
      have hunion : K ∪ (⋃ j ∈ insert i s, range (p j)) =
          range (p i) ∪ (K ∪ ⋃ j ∈ s, range (p j)) := by
        ext z
        simp only [mem_union, mem_iUnion, Finset.mem_insert]
        constructor
        · rintro (hzK | ⟨j, (rfl | hj), hzj⟩)
          · exact Or.inr (Or.inl hzK)
          · exact Or.inl hzj
          · exact Or.inr (Or.inr ⟨j, hj, hzj⟩)
        · rintro (hzi | hzK | ⟨j, hj, hzj⟩)
          · exact Or.inr ⟨i, Or.inl rfl, hzi⟩
          · exact Or.inl hzK
          · exact Or.inr ⟨j, Or.inr hj, hzj⟩
      rw [hunion]
      exact hnew

end FiniteAvalanches.Electrical.StatementGeometry

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb

open QuantumZipper.CA.Topo MatedCRTHarmonic.Topology

/-- A compact nonseparating set and disjoint arcs attached to it can be avoided
inside an open connected region containing them. -/
theorem isPreconnected_sdiff_union_finset_paths {ι : Type*} {U K : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hK : IsCompact K)
    (hsep : ∀ ⦃a b : ℂ⦄,
      a ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' K →
      b ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' K →
      ¬ Separates (Complex.equivRealProdCLM.symm.toHomeomorph '' K) a b)
    (hKU : K ⊆ U) (s : Finset ι) {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (range (p i)) (range (p j)))
    (hmeet : ∀ i ∈ s, IsPreconnected (range (p i) ∩ K))
    (hsub : ∀ i ∈ s, range (p i) ⊆ U) :
    IsPreconnected (U \ (K ∪ ⋃ i ∈ s, range (p i))) := by
  apply isPreconnected_sdiff_nonseparating_compact hU hconn
    (hK.union (s.isCompact_biUnion (fun i _ => isCompact_range (p i).continuous)))
    (not_separates_image_union_finset_paths hK hsep s p hp hd hmeet)
  exact union_subset hKU (iUnion₂_subset hsub)

end FiniteAvalanches.Electrical.StatementGeometry

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb

/-- A boundary access path can be attached to an interior arc tree at its first
contact, retaining its avoidance of the other arcs. -/
theorem exists_boundary_path_to_finiteArcTree_avoiding_finite
    {ι : Type*} [DecidableEq ι] {U K : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (s : Finset ι) {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (p i) ∩ U) (range (p j)))
    (hinside : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → p i t ∈ U)
    (hout : ∀ i ∈ s, y i ∉ U)
    {S : Set (ℝ × ℝ)} (hS : S.Finite)
    (hobsS : ∀ j ∈ s, Disjoint (range (p j)) S)
    {r : ℝ × ℝ} (hK : IsFiniteArcTree r K)
    (hrK : r ∈ K) (hr : r ∈ (U \ (⋃ i ∈ s, range (p i))) \ S)
    {i : ι} (hi : i ∈ s) (hyK : y i ∉ K) :
    ∃ z ∈ K, ∃ q : Path (y i) z, Function.Injective q ∧
      range q ∩ K = {z} ∧ IsFiniteArcTree r (range q ∪ K) ∧
      Disjoint (range q) S ∧ range q ∩ Uᶜ = {y i} ∧
      Disjoint (range q ∩ U) (⋃ j ∈ s.erase i, range (p j)) := by
  obtain ⟨a, ha, haS, haboundary, haavoid, _⟩ :=
    exists_path_to_boundary_avoiding_paths_disjoint_inside_and_finite
      hU hconn s p hp hd hinside hout hS hobsS hr hi
  have hrev : Function.Injective a.symm := by
    intro u v h
    exact unitInterval.symm_involutive.injective (ha h)
  obtain ⟨z, hz, q, hq, hqsub, hqK⟩ :=
    exists_initial_path_first_hit a.symm hrev hK.isCompact.isClosed hyK hrK
  have hsub : range q ⊆ range a := by simpa only [Path.symm_range] using hqsub
  refine ⟨z, hz, q, hq, hqK, IsFiniteArcTree.attach q hK hq hqK,
    haS.mono_left hsub, ?_, ?_⟩
  · apply subset_antisymm
    · exact (inter_subset_inter_left _ hsub).trans haboundary.le
    · exact singleton_subset_iff.mpr ⟨q.source_mem_range, hout i hi⟩
  · exact haavoid.mono_left (inter_subset_inter_left _ hsub)


/-- A boundary access path can be attached to an arc tree at its first contact. -/
theorem exists_boundary_path_to_finiteArcTree
    {ι : Type*} [DecidableEq ι] {U K : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (s : Finset ι) {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (p i) ∩ U) (range (p j)))
    (hinside : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → p i t ∈ U)
    (hout : ∀ i ∈ s, y i ∉ U)
    {r : ℝ × ℝ} (hK : IsFiniteArcTree r K)
    (hrK : r ∈ K) (hr : r ∈ U \ (⋃ i ∈ s, range (p i)))
    {i : ι} (hi : i ∈ s) (hyK : y i ∉ K) :
    ∃ z ∈ K, ∃ q : Path (y i) z, Function.Injective q ∧
      range q ∩ K = {z} ∧ IsFiniteArcTree r (range q ∪ K) ∧
      range q ∩ Uᶜ = {y i} ∧
      Disjoint (range q ∩ U) (⋃ j ∈ s.erase i, range (p j)) := by
  obtain ⟨z, hz, q, hq, hqK, ht, _, hb, ha⟩ :=
    exists_boundary_path_to_finiteArcTree_avoiding_finite hU hconn s p hp hd hinside hout
      (S := ∅) Set.finite_empty (by simp) hK hrK ⟨hr, by simp⟩ hi hyK
  exact ⟨z, hz, q, hq, hqK, ht, hb, ha⟩

/-- Boundary endpoints can be attached to one finite arc tree while
avoiding the arcs whose endpoints have not yet been attached. -/
theorem exists_finiteArcTree_to_boundary_paths_avoiding_finite
    {ι : Type*} [DecidableEq ι] {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (s : Finset ι) {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (p i) ∩ U) (range (p j)))
    (hinside : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → p i t ∈ U)
    (hout : ∀ i ∈ s, y i ∉ U)
    {S : Set (ℝ × ℝ)} (hS : S.Finite)
    (hobsS : ∀ j ∈ s, Disjoint (range (p j)) S)
    {r : ℝ × ℝ} (hr : r ∈ (U \ (⋃ i ∈ s, range (p i))) \ S) :
    ∀ t : Finset ι, t ⊆ s → ∃ K : Set (ℝ × ℝ),
      IsFiniteArcTree r K ∧ r ∈ K ∧ Disjoint K S ∧
      (∀ i ∈ t, y i ∈ K) ∧
      K ∩ Uᶜ ⊆ y '' (↑t : Set ι) ∧
      Disjoint (K ∩ U) (⋃ j ∈ s \ t, range (p j)) := by
  classical
  intro t
  induction t using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨{r}, IsFiniteArcTree.singleton, by simp, ?_, ?_, ?_, ?_⟩
      · exact Set.disjoint_left.mpr (by simpa using hr.2)
      · simp
      · intro z hz
        have : z = r := mem_singleton_iff.mp hz.1
        exact (hz.2 (this.symm ▸ hr.1.1)).elim
      · apply Set.disjoint_left.mpr
        rintro z ⟨hz, _⟩ hzobs
        have : z = r := mem_singleton_iff.mp hz
        apply hr.1.2
        subst z
        obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp hzobs
        exact mem_iUnion₂.mpr ⟨j, (Finset.mem_sdiff.mp hj).1, hzj⟩
  | @insert i t hit ih =>
      intro hts
      have hi : i ∈ s := hts (Finset.mem_insert_self i t)
      have hts' : t ⊆ s := fun j hj => hts (Finset.mem_insert_of_mem hj)
      obtain ⟨K, hK, hrK, hKS, htargets, hboundary, havoid⟩ := ih hts'
      by_cases hyK : y i ∈ K
      · refine ⟨K, hK, hrK, hKS, ?_, ?_, ?_⟩
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact hyK
          · exact htargets j hj
        · rintro w hw
          obtain ⟨j, hj, h⟩ := hboundary hw
          exact ⟨j, Finset.mem_insert_of_mem hj, h⟩
        · apply havoid.mono_right
          intro w hw
          obtain ⟨j, hj, hwj⟩ := mem_iUnion₂.mp hw
          have hjs := (Finset.mem_sdiff.mp hj).1
          have hjnot := (Finset.mem_sdiff.mp hj).2
          exact mem_iUnion₂.mpr ⟨j, Finset.mem_sdiff.mpr
            ⟨hjs, fun hjt => hjnot (Finset.mem_insert_of_mem hjt)⟩, hwj⟩
      obtain ⟨z, hz, q, hq, hqK, htree, hqS, hqboundary, hqavoid⟩ :=
        exists_boundary_path_to_finiteArcTree_avoiding_finite hU hconn s p hp hd
          hinside hout hS hobsS hK hrK hr hi hyK
      refine ⟨range q ∪ K, htree, Or.inr hrK, disjoint_union_left.mpr ⟨hqS, hKS⟩,
        ?_, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact Or.inl q.source_mem_range
        · exact Or.inr (htargets j hj)
      · rintro w ⟨hw | hw, hwU⟩
        · have hw' : w = y i := mem_singleton_iff.mp (hqboundary ▸ ⟨hw, hwU⟩)
          exact ⟨i, Finset.mem_insert_self i t, hw'.symm⟩
        · obtain ⟨j, hj, h⟩ := hboundary ⟨hw, hwU⟩
          exact ⟨j, Finset.mem_insert_of_mem hj, h⟩
      · apply Set.disjoint_left.mpr
        rintro w ⟨hw | hw, hwU⟩ hwobs
        all_goals
          obtain ⟨j, hj, hwj⟩ := mem_iUnion₂.mp hwobs
          have hjs := (Finset.mem_sdiff.mp hj).1
          have hjnot := (Finset.mem_sdiff.mp hj).2
          have hjt : j ∉ t := fun h => hjnot (Finset.mem_insert_of_mem h)
          have hji : j ≠ i := fun h => hjnot (h ▸ Finset.mem_insert_self i t)
        · exact Set.disjoint_left.mp hqavoid ⟨hw, hwU⟩
            (mem_iUnion₂.mpr ⟨j, Finset.mem_erase.mpr ⟨hji, hjs⟩, hwj⟩)
        · exact Set.disjoint_left.mp havoid ⟨hw, hwU⟩
            (mem_iUnion₂.mpr ⟨j, Finset.mem_sdiff.mpr ⟨hjs, hjt⟩, hwj⟩)


/-- Boundary endpoints can be attached to a finite arc tree. -/
theorem exists_finiteArcTree_to_boundary_paths
    {ι : Type*} [DecidableEq ι] {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (s : Finset ι) {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (p i) ∩ U) (range (p j)))
    (hinside : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → p i t ∈ U)
    (hout : ∀ i ∈ s, y i ∉ U)
    {r : ℝ × ℝ} (hr : r ∈ U \ (⋃ i ∈ s, range (p i))) :
    ∀ t : Finset ι, t ⊆ s → ∃ K : Set (ℝ × ℝ),
      IsFiniteArcTree r K ∧ r ∈ K ∧
      (∀ i ∈ t, y i ∈ K) ∧
      K ∩ Uᶜ ⊆ y '' (↑t : Set ι) ∧
      Disjoint (K ∩ U) (⋃ j ∈ s \ t, range (p j)) := by
  intro t ht
  obtain ⟨K, hK, hrK, _, hy, hb, ha⟩ :=
    exists_finiteArcTree_to_boundary_paths_avoiding_finite hU hconn s p hp hd hinside hout
      (S := ∅) Set.finite_empty (by simp) ⟨hr, by simp⟩ t ht
  exact ⟨K, hK, hrK, hy, hb, ha⟩

end FiniteAvalanches.Electrical.StatementGeometry


open Filter
open scoped Topology

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb

/-- A terminal subpath included in an injective path has a shorter terminal
subpath included in any nontrivial initial segment of the reversed path. -/
theorem terminal_subpath_in_initial_reverse {X : Type*} [TopologicalSpace X] [T2Space X]
    {r x y : X} (a : Path r y) (p : Path x y) (ha : Function.Injective a)
    {t T : unitInterval} (ht : t ≠ 1) (hT : T ≠ 0)
    (hsub : range (p.subpath t 1) ⊆ range a) :
    ∃ t' : unitInterval, t' ≠ 1 ∧
      range (p.subpath t' 1) ⊆ range (a.symm.subpath 0 T) := by
  let K : Set X := a.symm '' Ici T
  have hK : IsCompact K := (isCompact_univ.of_isClosed_subset isClosed_Ici (subset_univ _)).image
    a.symm.continuous
  have hrev : Function.Injective a.symm := by
    intro u v h
    exact unitInterval.symm_involutive.injective (ha h)
  have hyK : y ∉ K := by
    rintro ⟨u, hu, h⟩
    have hu0 : u = 0 := hrev (h.trans a.symm.source.symm)
    have : T ≤ 0 := by
      change T ≤ u at hu
      simpa only [hu0] using hu
    exact hT (le_antisymm this (bot_le))
  have hpre : p ⁻¹' Kᶜ ∈ 𝓝 (1 : unitInterval) :=
    (hK.isClosed.isOpen_compl.preimage p.continuous).mem_nhds (by
      change p (1 : unitInterval) ∉ K
      simpa only [Path.target] using hyK)
  obtain ⟨u, hu, husub⟩ := exists_Ioc_subset_of_mem_nhds hpre
    ⟨(0 : unitInterval), by norm_num⟩
  have htlt : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2
    (fun h => ht (Subtype.ext h))
  have hult : (u : ℝ) < 1 := hu
  let t' : unitInterval := ⟨(max (t : ℝ) (u : ℝ) + 1) / 2, by
    constructor
    · have := le_max_left (t : ℝ) (u : ℝ)
      linarith [t.property.1]
    · have : max (t : ℝ) (u : ℝ) < 1 := max_lt htlt hult
      linarith⟩
  have htt : t ≤ t' := by
    change (t : ℝ) ≤ (max (t : ℝ) (u : ℝ) + 1) / 2
    have := le_max_left (t : ℝ) (u : ℝ)
    linarith
  have hut : u < t' := by
    change (u : ℝ) < (max (t : ℝ) (u : ℝ) + 1) / 2
    have := le_max_right (t : ℝ) (u : ℝ)
    linarith
  have httop : t' ≠ 1 := by
    intro h
    have h' := congrArg Subtype.val h
    change (max (t : ℝ) (u : ℝ) + 1) / 2 = 1 at h'
    have : max (t : ℝ) (u : ℝ) < 1 := max_lt htlt hult
    linarith
  refine ⟨t', httop, ?_⟩
  rw [Path.range_subpath_of_le _ _ _ (by exact le_top)]
  rintro z ⟨v, hv, rfl⟩
  have hvold : v ∈ Icc t 1 := ⟨htt.trans hv.1, le_top⟩
  have hva : p v ∈ range a := hsub (by
    rw [Path.range_subpath_of_le _ _ _ (by exact le_top)]
    exact ⟨v, hvold, rfl⟩)
  have hva' : p v ∈ range a.symm := by simpa only [Path.symm_range] using hva
  obtain ⟨w, hw⟩ := hva'
  have hvnot : p v ∉ K := husub ⟨hut.trans_le hv.1, le_top⟩
  have hwlt : w < T := by
    by_contra hn
    exact hvnot ⟨w, le_of_not_gt hn, hw⟩
  rw [Path.range_subpath_of_le _ _ _ (by exact bot_le)]
  exact ⟨w, ⟨bot_le, hwlt.le⟩, hw⟩

/-- A boundary attachment retaining a terminal subpath of the selected arc. -/
theorem exists_boundary_path_to_finiteArcTree_avoiding_finite_with_tail
    {ι : Type*} [DecidableEq ι] {U K : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (s : Finset ι) {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (p i) ∩ U) (range (p j)))
    (hinside : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → p i t ∈ U)
    (hout : ∀ i ∈ s, y i ∉ U)
    {S : Set (ℝ × ℝ)} (hS : S.Finite)
    (hobsS : ∀ j ∈ s, Disjoint (range (p j)) S)
    {r : ℝ × ℝ} (hK : IsFiniteArcTree r K)
    (hrK : r ∈ K) (hr : r ∈ (U \ (⋃ i ∈ s, range (p i))) \ S)
    {i : ι} (hi : i ∈ s) (hyK : y i ∉ K) :
    ∃ z ∈ K, ∃ q : Path (y i) z, Function.Injective q ∧
      range q ∩ K = {z} ∧ IsFiniteArcTree r (range q ∪ K) ∧
      Disjoint (range q) S ∧ range q ∩ Uᶜ = {y i} ∧
      Disjoint (range q ∩ U) (⋃ j ∈ s.erase i, range (p j)) ∧
      ∃ t : unitInterval, t ≠ 1 ∧ range ((p i).subpath t 1) ⊆ range q := by
  obtain ⟨a, ha, haS, haboundary, haavoid, t, ht, htail⟩ :=
    exists_path_to_boundary_avoiding_paths_disjoint_inside_and_finite
      hU hconn s p hp hd hinside hout hS hobsS hr hi
  have hrev : Function.Injective a.symm := by
    intro u v h
    exact unitInterval.symm_involutive.injective (ha h)
  obtain ⟨z, hz, q, hq, hqsub, hqK, T, hT, hrange⟩ :=
    exists_initial_path_first_hit_with_subpath a.symm hrev hK.isCompact.isClosed hyK hrK
  have hsub : range q ⊆ range a := by simpa only [Path.symm_range] using hqsub
  refine ⟨z, hz, q, hq, hqK, IsFiniteArcTree.attach q hK hq hqK,
    haS.mono_left hsub, ?_, ?_, ?_⟩
  · apply subset_antisymm
    · exact (inter_subset_inter_left _ hsub).trans haboundary.le
    · exact singleton_subset_iff.mpr ⟨q.source_mem_range, hout i hi⟩
  · exact haavoid.mono_left (inter_subset_inter_left _ hsub)
  · obtain ⟨t', ht', htail'⟩ := terminal_subpath_in_initial_reverse a (p i) ha ht hT htail
    exact ⟨t', ht', hrange ▸ htail'⟩


end FiniteAvalanches.Electrical.StatementGeometry

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb

/-- Boundary arcs can be attached to a finite arc tree with a terminal
subarc of each selected arc retained in the tree. -/
theorem exists_finiteArcTree_to_boundary_paths_with_tails
    {ι : Type*} [DecidableEq ι] {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (s : Finset ι) {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (p i) ∩ U) (range (p j)))
    (hinside : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → p i t ∈ U)
    (hout : ∀ i ∈ s, y i ∉ U)
    {S : Set (ℝ × ℝ)} (hS : S.Finite)
    (hobsS : ∀ j ∈ s, Disjoint (range (p j)) S)
    {r : ℝ × ℝ} (hr : r ∈ (U \ (⋃ i ∈ s, range (p i))) \ S) :
    ∀ t : Finset ι, t ⊆ s → ∃ K : Set (ℝ × ℝ),
      IsFiniteArcTree r K ∧ r ∈ K ∧ Disjoint K S ∧
      (∀ i ∈ t, ∃ u : unitInterval, u ≠ 1 ∧ range ((p i).subpath u 1) ⊆ K) ∧
      K ∩ Uᶜ ⊆ y '' (↑t : Set ι) ∧
      Disjoint (K ∩ U) (⋃ j ∈ s \ t, range (p j)) := by
  classical
  intro t
  induction t using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨{r}, IsFiniteArcTree.singleton, by simp, ?_, ?_, ?_, ?_⟩
      · exact Set.disjoint_left.mpr (by simpa using hr.2)
      · simp
      · intro z hz
        have : z = r := mem_singleton_iff.mp hz.1
        exact (hz.2 (this.symm ▸ hr.1.1)).elim
      · apply Set.disjoint_left.mpr
        rintro z ⟨hz, _⟩ hzobs
        have : z = r := mem_singleton_iff.mp hz
        apply hr.1.2
        subst z
        obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp hzobs
        exact mem_iUnion₂.mpr ⟨j, (Finset.mem_sdiff.mp hj).1, hzj⟩
  | @insert i t hit ih =>
      intro hts
      have hi : i ∈ s := hts (Finset.mem_insert_self i t)
      have hts' : t ⊆ s := fun j hj => hts (Finset.mem_insert_of_mem hj)
      obtain ⟨K, hK, hrK, hKS, htails, hboundary, havoid⟩ := ih hts'
      have hattach : ∃ L : Set (ℝ × ℝ),
          IsFiniteArcTree r (L ∪ K) ∧ Disjoint L S ∧
          L ∩ Uᶜ = {y i} ∧
          Disjoint (L ∩ U) (⋃ j ∈ s.erase i, range (p j)) ∧
          ∃ u : unitInterval, u ≠ 1 ∧ range ((p i).subpath u 1) ⊆ L := by
        by_cases hyK : y i ∈ K
        · have hinter : range (p i) ∩ K = {y i} := by
            apply subset_antisymm
            · rintro w ⟨⟨v, rfl⟩, hwK⟩
              by_cases hv : v = 1
              · simp [hv]
              · have hwU := hinside i hi v hv
                have hwobs : p i v ∈ ⋃ j ∈ s \ t, range (p j) :=
                  mem_iUnion₂.mpr ⟨i, Finset.mem_sdiff.mpr ⟨hi, hit⟩, ⟨v, rfl⟩⟩
                exact (Set.disjoint_left.mp havoid ⟨hwK, hwU⟩ hwobs).elim
            · exact singleton_subset_iff.mpr ⟨(p i).target_mem_range, hyK⟩
          refine ⟨range (p i), IsFiniteArcTree.attach (p i) hK (hp i hi) hinter,
            hobsS i hi, ?_, ?_, 0, by norm_num, ?_⟩
          · exact range_inter_compl_of_mem_except_target (p i) (hinside i hi) (hout i hi)
          · apply Set.disjoint_left.mpr
            rintro w hw hobs
            obtain ⟨j, hj, hwj⟩ := mem_iUnion₂.mp hobs
            exact Set.disjoint_left.mp (hd i hi j (Finset.mem_erase.mp hj).2
              (Ne.symm (Finset.mem_erase.mp hj).1)) hw hwj
          · exact subpath_range_subset _ _ _
        · obtain ⟨z, hz, q, hq, hqK, ht, hqS, hb, ha, u, hu, htail⟩ :=
            exists_boundary_path_to_finiteArcTree_avoiding_finite_with_tail hU hconn s p hp hd
              hinside hout hS hobsS hK hrK hr hi hyK
          exact ⟨range q, ht, hqS, hb, ha, u, hu, htail⟩
      obtain ⟨L, htree, hLS, hLboundary, hLavoid, u, hu, htail⟩ := hattach
      refine ⟨L ∪ K, htree, Or.inr hrK, disjoint_union_left.mpr ⟨hLS, hKS⟩,
        ?_, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact ⟨u, hu, htail.trans subset_union_left⟩
        · obtain ⟨v, hv, hvsub⟩ := htails j hj
          exact ⟨v, hv, hvsub.trans subset_union_right⟩
      · rintro w ⟨hw | hw, hwU⟩
        · have hw' : w = y i := mem_singleton_iff.mp (hLboundary ▸ ⟨hw, hwU⟩)
          exact ⟨i, Finset.mem_insert_self i t, hw'.symm⟩
        · obtain ⟨j, hj, h⟩ := hboundary ⟨hw, hwU⟩
          exact ⟨j, Finset.mem_insert_of_mem hj, h⟩
      · apply Set.disjoint_left.mpr
        rintro w ⟨hw | hw, hwU⟩ hwobs
        all_goals
          obtain ⟨j, hj, hwj⟩ := mem_iUnion₂.mp hwobs
          have hjs := (Finset.mem_sdiff.mp hj).1
          have hjnot := (Finset.mem_sdiff.mp hj).2
          have hjt : j ∉ t := fun h => hjnot (Finset.mem_insert_of_mem h)
          have hji : j ≠ i := fun h => hjnot (h ▸ Finset.mem_insert_self i t)
        · exact Set.disjoint_left.mp hLavoid ⟨hw, hwU⟩
            (mem_iUnion₂.mpr ⟨j, Finset.mem_erase.mpr ⟨hji, hjs⟩, hwj⟩)
        · exact Set.disjoint_left.mp havoid ⟨hw, hwU⟩
            (mem_iUnion₂.mpr ⟨j, Finset.mem_sdiff.mpr ⟨hjs, hjt⟩, hwj⟩)

end FiniteAvalanches.Electrical.StatementGeometry

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb

/-- Finitely many terminal subpaths can be shortened to a common parameter. -/
theorem exists_common_terminal_subpath {ι X : Type*} [TopologicalSpace X]
    (s : Finset ι) {x y : ι → X} (p : ∀ i, Path (x i) (y i)) (K : Set X)
    (h : ∀ i ∈ s, ∃ u : unitInterval, u ≠ 1 ∧ range ((p i).subpath u 1) ⊆ K) :
    ∃ u : unitInterval, u ≠ 1 ∧ ∀ i ∈ s, range ((p i).subpath u 1) ⊆ K := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨0, by norm_num, by simp⟩
  | @insert i s hi ih =>
      obtain ⟨u, hu, hus⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      obtain ⟨v, hv, hvi⟩ := h i (Finset.mem_insert_self i s)
      have hu1 : u < 1 := lt_of_le_of_ne le_top hu
      have hv1 : v < 1 := lt_of_le_of_ne le_top hv
      refine ⟨max u v, (max_lt hu1 hv1).ne, ?_⟩
      intro j hj
      have hsub (a b : unitInterval) (hab : a ≤ b) :
          range ((p j).subpath b 1) ⊆ range ((p j).subpath a 1) := by
        rw [Path.range_subpath_of_le _ _ _ (show b ≤ (1 : unitInterval) from le_top),
          Path.range_subpath_of_le _ _ _ (show a ≤ (1 : unitInterval) from le_top)]
        exact Set.image_mono (Set.Icc_subset_Icc hab le_rfl)
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (hsub v (max u v) (le_max_right _ _)).trans hvi
      · exact (hsub u (max u v) (le_max_left _ _)).trans (hus j hj)

/-- A finite family of boundary arcs has a common terminal scale inside one tree. -/
theorem exists_finiteArcTree_to_boundary_paths_with_common_tail
    {ι : Type*} [DecidableEq ι] {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (s : Finset ι) {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (p i) ∩ U) (range (p j)))
    (hinside : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → p i t ∈ U)
    (hout : ∀ i ∈ s, y i ∉ U)
    {S : Set (ℝ × ℝ)} (hS : S.Finite)
    (hobsS : ∀ j ∈ s, Disjoint (range (p j)) S)
    {r : ℝ × ℝ} (hr : r ∈ (U \ (⋃ i ∈ s, range (p i))) \ S)
    (t : Finset ι) (ht : t ⊆ s) :
    ∃ K : Set (ℝ × ℝ), ∃ u : unitInterval,
      u ≠ 1 ∧ IsFiniteArcTree r K ∧ r ∈ K ∧ Disjoint K S ∧
      (∀ i ∈ t, range ((p i).subpath u 1) ⊆ K) ∧
      K ∩ Uᶜ ⊆ y '' (↑t : Set ι) ∧
      Disjoint (K ∩ U) (⋃ j ∈ s \ t, range (p j)) := by
  obtain ⟨K, hK, hrK, hKS, htail, hboundary, havoid⟩ :=
    exists_finiteArcTree_to_boundary_paths_with_tails hU hconn s p hp hd hinside hout
      hS hobsS hr t ht
  obtain ⟨u, hu, hcommon⟩ := exists_common_terminal_subpath t p K htail
  exact ⟨K, u, hu, hK, hrK, hKS, hcommon, hboundary, havoid⟩

/-- Each interior point on a finite family of boundary arcs has a neighborhood
in the region that avoids the other arcs and a prescribed finite set. -/
theorem exists_ball_around_boundary_path_point {ι : Type*} [DecidableEq ι]
    {U S : Set (ℝ × ℝ)} (hU : IsOpen U) (s : Finset ι)
    {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (p i) ∩ U) (range (p j)))
    (hinside : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → p i t ∈ U)
    (hS : S.Finite) (hobsS : ∀ i ∈ s, Disjoint (range (p i)) S)
    {i : ι} (hi : i ∈ s) {t : unitInterval} (ht : t ≠ 1) :
    ∃ ε : ℝ, 0 < ε ∧
      Metric.ball (p i t) ε ⊆ U \ (S ∪ ⋃ j ∈ s.erase i, range (p j)) := by
  have hc : IsClosed (S ∪ ⋃ j ∈ s.erase i, range (p j)) := by
    exact hS.isClosed.union
      ((s.erase i).isCompact_biUnion (fun j _ => isCompact_range (p j).continuous)).isClosed
  have hpoint : p i t ∈ U \ (S ∪ ⋃ j ∈ s.erase i, range (p j)) := by
    refine ⟨hinside i hi t ht, ?_⟩
    rintro (hS' | hother)
    · exact Set.disjoint_left.mp (hobsS i hi) ⟨t, rfl⟩ hS'
    · obtain ⟨j, hj, hpj⟩ := mem_iUnion₂.mp hother
      exact Set.disjoint_left.mp (hd i hi j (Finset.mem_erase.mp hj).2
        (Ne.symm (Finset.mem_erase.mp hj).1)) ⟨⟨t, rfl⟩, hinside i hi t ht⟩ hpj
  exact Metric.isOpen_iff.mp (hU.sdiff hc) _ hpoint


/-- Chosen interior points on finitely many boundary arcs have pairwise disjoint
neighborhoods avoiding the other arcs and a prescribed finite set. -/
theorem exists_disjoint_balls_around_boundary_path_points {ι : Type*} [DecidableEq ι]
    {U S : Set (ℝ × ℝ)} (hU : IsOpen U) (s : Finset ι)
    {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (p i) ∩ U) (range (p j)))
    (hinside : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → p i t ∈ U)
    (hS : S.Finite) (hobsS : ∀ i ∈ s, Disjoint (range (p i)) S)
    (t : ι → unitInterval) (ht : ∀ i ∈ s, t i ≠ 1) :
    ∃ ε : ι → ℝ, (∀ i ∈ s, 0 < ε i ∧
      Metric.ball (p i (t i)) (ε i) ⊆ U \ (S ∪ ⋃ j ∈ s.erase i, range (p j))) ∧
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        Disjoint (Metric.ball (p i (t i)) (ε i)) (Metric.ball (p j (t j)) (ε j))) := by
  classical
  let a : ι → ℝ × ℝ := fun i => p i (t i)
  have hdistinct : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → a i ≠ a j := by
    intro i hi j hj hij heq
    apply Set.disjoint_left.mp (hd i hi j hj hij)
      ⟨⟨t i, rfl⟩, hinside i hi (t i) (ht i hi)⟩
    exact ⟨t j, heq.symm⟩
  obtain ⟨W, hW, hdisj⟩ := ((s.finite_toSet).image a).t2_separation
  have hball : ∀ i, ∃ ε : ℝ, 0 < ε ∧
      (i ∈ s → Metric.ball (a i) ε ⊆
        (U \ (S ∪ ⋃ j ∈ s.erase i, range (p j))) ∩ W (a i)) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨δ, hδ, hδsub⟩ :=
        exists_ball_around_boundary_path_point hU s p hd hinside hS hobsS hi (ht i hi)
      obtain ⟨η, hη, hηsub⟩ := Metric.isOpen_iff.mp (hW (a i)).2 (a i) (hW (a i)).1
      refine ⟨min δ η, lt_min hδ hη, fun _ => ?_⟩
      exact subset_inter ((Metric.ball_subset_ball (min_le_left _ _)).trans hδsub)
        ((Metric.ball_subset_ball (min_le_right _ _)).trans hηsub)
    · exact ⟨1, by norm_num, fun h => (hi h).elim⟩
  choose ε hε hsub using hball
  refine ⟨ε, ?_, ?_⟩
  · intro i hi
    exact ⟨hε i, (hsub i hi).trans inter_subset_left⟩
  · intro i hi j hj hij
    apply (hdisj (Set.mem_image_of_mem a hi) (Set.mem_image_of_mem a hj)
      (hdistinct i hi j hj hij)).mono
    · exact (hsub i hi).trans inter_subset_right
    · exact (hsub j hj).trans inter_subset_right


/-- Selected boundary endpoints admit simple paths from the root inside one
finite arc tree, avoiding the prescribed set and all unselected boundary arcs. -/
theorem exists_rooted_paths_to_boundary_in_finiteArcTree
    {ι : Type*} [DecidableEq ι] {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (s : Finset ι) {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (p i) ∩ U) (range (p j)))
    (hinside : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → p i t ∈ U)
    (hout : ∀ i ∈ s, y i ∉ U)
    {S : Set (ℝ × ℝ)} (hS : S.Finite)
    (hobsS : ∀ j ∈ s, Disjoint (range (p j)) S)
    {r : ℝ × ℝ} (hr : r ∈ (U \ (⋃ i ∈ s, range (p i))) \ S)
    (t : Finset ι) (ht : t ⊆ s) :
    ∃ K : Set (ℝ × ℝ), ∃ u : unitInterval,
      u ≠ 1 ∧ IsFiniteArcTree r K ∧ Disjoint K S ∧
      (∀ i ∈ t, range ((p i).subpath u 1) ⊆ K) ∧
      (∀ i ∈ t, ∃ q : Path r (y i), Function.Injective q ∧ range q ⊆ K) ∧
      K ∩ Uᶜ ⊆ y '' (↑t : Set ι) ∧
      Disjoint (K ∩ U) (⋃ j ∈ s \ t, range (p j)) := by
  obtain ⟨K, u, hu, hK, hrK, hKS, htail, hboundary, havoid⟩ :=
    exists_finiteArcTree_to_boundary_paths_with_common_tail hU hconn s p hp hd hinside hout
      hS hobsS hr t ht
  refine ⟨K, u, hu, hK, hKS, htail, ?_, hboundary, havoid⟩
  intro i hi
  have hyK : y i ∈ K := htail i hi (by
    have h := ((p i).subpath u 1).target_mem_range
    simpa only [Path.target] using h)
  have hry : r ≠ y i := fun h => hout i (ht hi) (h ▸ hr.1.1)
  exact hK.exists_injective_path hrK hyK hry

end FiniteAvalanches.Electrical.StatementGeometry
