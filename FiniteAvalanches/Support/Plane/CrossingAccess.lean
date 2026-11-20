import FiniteAvalanches.Support.Plane.TreePaths

/-!
# Transverse access to a charted arc

A point on a charted vertical arc has a simple transverse access path in any
open neighborhood of the point.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb

open Set

/-- A vertical arc can be approached transversely inside any open neighborhood. -/
theorem exists_transverse_path_to_vertical_arc {U A : Set (ℝ × ℝ)}
    (hU : IsOpen U) (h : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) {a : ℝ × ℝ}
    (ha : a ∈ U ∩ A) (c : ℝ) (hA : ∀ z ∈ A, (h z).1 = c) :
    ∃ b : ℝ × ℝ, ∃ p : Path a b, b ≠ a ∧ Function.Injective p ∧
      range p ⊆ U ∧ range p ∩ A = {a} := by
  let v : ℝ × ℝ := (0, 1)
  have hv : v ≠ 0 := by simp [v]
  obtain ⟨q, hq, hseg, hdir⟩ :=
    exists_segment_not_parallel (h.isOpenMap U hU) (Set.mem_image_of_mem h ha.1)
      (Set.finite_singleton v)
  have hfirst : q.1 ≠ (h a).1 := by
    have hd := hdir v (mem_singleton v) hv
    dsimp [v] at hd
    simp only [mul_one, mul_zero, sub_zero] at hd
    exact sub_ne_zero.mp hd
  let b := h.symm q
  let p : Path a b := ((Path.segment (h a) q).map h.symm.continuous).cast
    (h.symm_apply_apply a).symm rfl
  have hp : Function.Injective p := by
    change Function.Injective (h.symm ∘ Path.segment (h a) q)
    exact h.symm.injective.comp (Path.segment_injective_of_ne (Ne.symm hq))
  have hsub : range p ⊆ U := by
    rintro z ⟨t, rfl⟩
    have ht : Path.segment (h a) q t ∈ h '' U := hseg (by
      rw [← Path.range_segment]
      exact ⟨t, rfl⟩)
    obtain ⟨w, hw, heq⟩ := ht
    change h.symm (Path.segment (h a) q t) ∈ U
    simpa [← heq] using hw
  have hmeet : range p ∩ A ⊆ {a} := by
    rintro z ⟨⟨t, rfl⟩, ht⟩
    have htfirst : ((Path.segment (h a) q) t).1 = (h a).1 := by
      have := hA (p t) ht
      have ha' := hA a ha.2
      change (h (h.symm ((Path.segment (h a) q) t))).1 = c at this
      rw [h.apply_symm_apply] at this
      exact this.trans ha'.symm
    have htzero : t = 0 := by
      apply Subtype.ext
      change (t : ℝ) * (q.1 - (h a).1) + (h a).1 = (h a).1 at htfirst
      have hneq : q.1 - (h a).1 ≠ 0 := sub_ne_zero.mpr hfirst
      have : (t : ℝ) * (q.1 - (h a).1) = 0 := by linarith [htfirst]
      exact (mul_eq_zero.mp this).resolve_right hneq
    simp [htzero]
  refine ⟨b, p, ?_, hp, hsub, subset_antisymm hmeet ?_⟩
  · intro heq
    apply hq
    simpa [b] using congrArg h heq
  · intro z hz
    simp only [mem_singleton_iff] at hz
    subst z
    exact ⟨p.source_mem_range, ha.2⟩

/-- A finite family of charted boundary arcs admits mutually disjoint local
transverse paths avoiding the other arcs. -/
theorem exists_disjoint_transverse_paths_to_boundary_arcs
    {ι : Type*} [DecidableEq ι] {U S : Set (ℝ × ℝ)} (hU : IsOpen U)
    (s : Finset ι) {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (p i) ∩ U) (range (p j)))
    (hinside : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → p i t ∈ U)
    (hS : S.Finite) (hobsS : ∀ i ∈ s, Disjoint (range (p i)) S)
    (t : ι → unitInterval) (ht : ∀ i ∈ s, t i ≠ 1)
    (chart : ι → (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (c : ι → ℝ)
    (hvertical : ∀ i ∈ s, ∀ z ∈ range (p i), (chart i z).1 = c i) :
    ∃ b : ι → ℝ × ℝ, ∃ w : ∀ i, Path (p i (t i)) (b i),
      (∀ i ∈ s, b i ≠ p i (t i) ∧ Function.Injective (w i) ∧
        range (w i) ⊆ U \ (S ∪ ⋃ j ∈ s.erase i, range (p j)) ∧
        range (w i) ∩ range (p i) = {p i (t i)}) ∧
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (range (w i)) (range (w j))) := by
  classical
  obtain ⟨ε, hε, hdisj⟩ :=
    exists_disjoint_balls_around_boundary_path_points hU s p hd hinside hS hobsS t ht
  have hex : ∀ i, ∃ b : ℝ × ℝ, ∃ w : Path (p i (t i)) b,
      i ∈ s → b ≠ p i (t i) ∧ Function.Injective w ∧
        range w ⊆ Metric.ball (p i (t i)) (ε i) ∧
        range w ∩ range (p i) = {p i (t i)} := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨b, w, hb, hw, hwsub, hwmeet⟩ :=
        exists_transverse_path_to_vertical_arc
          (U := Metric.ball (p i (t i)) (ε i)) (A := range (p i))
          (a := p i (t i)) Metric.isOpen_ball (chart i)
          ⟨Metric.mem_ball_self (hε i hi).1, ⟨t i, rfl⟩⟩ (c i) (hvertical i hi)
      exact ⟨b, w, fun _ => ⟨hb, hw, hwsub, hwmeet⟩⟩
    · exact ⟨p i (t i), Path.refl _, fun h => (hi h).elim⟩
  choose b w hw using hex
  refine ⟨b, w, ?_, ?_⟩
  · intro i hi
    obtain ⟨hb, hinj, hsub, hmeet⟩ := hw i hi
    exact ⟨hb, hinj, hsub.trans (hε i hi).2, hmeet⟩
  · intro i hi j hj hij
    exact (hdisj i hi j hj hij).mono (hw i hi).2.2.1 (hw j hj).2.2.1

/-- Removing finitely many arc trees preserves preconnectedness when they are
disjoint inside the region and meet its complement in preconnected sets. -/
theorem isPreconnected_sdiff_finset_arcTrees_of_disjoint_inside
    {ι : Type*} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hconn : IsPreconnected U)
    (s : Finset ι) (r : ι → ℝ × ℝ) (K : ι → Set (ℝ × ℝ))
    (hK : ∀ i ∈ s, IsFiniteArcTree (r i) (K i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (K i ∩ U) (K j))
    (hinter : ∀ i ∈ s, IsPreconnected (K i ∩ Uᶜ)) :
    IsPreconnected (U \ (⋃ i ∈ s, K i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hconn
  | @insert i s hi ih =>
      have hc : IsCompact (⋃ j ∈ s, K j) :=
        s.isCompact_biUnion (fun j hj => (hK j (Finset.mem_insert_of_mem hj)).isCompact)
      have hprev := ih (fun j hj => hK j (Finset.mem_insert_of_mem hj))
        (fun j hj k hk hne => hd j (Finset.mem_insert_of_mem hj)
          k (Finset.mem_insert_of_mem hk) hne)
        (fun j hj => hinter j (Finset.mem_insert_of_mem hj))
      have hinter' : K i ∩ (U \ (⋃ j ∈ s, K j))ᶜ = K i ∩ Uᶜ := by
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
      have htree := hK i (Finset.mem_insert_self i s)
      have hnew : IsPreconnected ((U \ (⋃ j ∈ s, K j)) \ K i) :=
        isPreconnected_sdiff_nonseparating_compact_of_preconnected_inter_compl
          (hU.sdiff hc.isClosed) hprev htree.isCompact htree.not_separates
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

/-- Points outside finitely many boundary-attached arc trees admit a disjoint
path star avoiding those trees and a further finite set. -/
theorem exists_disjoint_path_star_avoiding_arcTrees
    {ι κ : Type*} {U S : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hconn : IsPreconnected U) (s : Finset ι) (root : ι → ℝ × ℝ)
    (K : ι → Set (ℝ × ℝ))
    (hK : ∀ i ∈ s, IsFiniteArcTree (root i) (K i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (K i ∩ U) (K j))
    (hinter : ∀ i ∈ s, IsPreconnected (K i ∩ Uᶜ))
    (t : Finset κ) (hS : S.Finite) {r : ℝ × ℝ} {x : κ → ℝ × ℝ}
    (hr : r ∈ (U \ (⋃ i ∈ s, K i)) \ S)
    (hx : ∀ i ∈ t, x i ∈ (U \ (⋃ i ∈ s, K i)) \ S)
    (hxr : ∀ i ∈ t, x i ≠ r)
    (hinj : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → x i ≠ x j) :
    ∃ p : ∀ i, Path (x i) r,
      (∀ i ∈ t, Function.Injective (p i)) ∧
      (∀ i ∈ t, range (p i) ⊆ (U \ (⋃ i ∈ s, K i)) \ S) ∧
      (∀ i ∈ t, ∀ j ∈ t, i ≠ j → range (p i) ∩ range (p j) = {r}) := by
  have hc : IsCompact (⋃ i ∈ s, K i) :=
    s.isCompact_biUnion (fun i hi => (hK i hi).isCompact)
  exact exists_disjoint_path_star (hU.sdiff hc.isClosed)
    (isPreconnected_sdiff_finset_arcTrees_of_disjoint_inside hU hconn s root K hK hd hinter)
    t hS hr hx hxr hinj

/-- Removing boundary arcs together with pairwise disjoint transverse
attachments preserves preconnectedness. -/
theorem isPreconnected_sdiff_boundary_arcs_with_attachments
    {ι : Type*} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hconn : IsPreconnected U)
    (s : Finset ι) {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (t : ι → unitInterval) {b : ι → ℝ × ℝ} (w : ∀ i, Path (p i (t i)) (b i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hw : ∀ i ∈ s, Function.Injective (w i))
    (hwU : ∀ i ∈ s, range (w i) ⊆ U)
    (hmeet : ∀ i ∈ s, range (w i) ∩ range (p i) = {p i (t i)})
    (hpp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (p i) ∩ U) (range (p j)))
    (hwp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (range (w i)) (range (p j)))
    (hww : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (range (w i)) (range (w j)))
    (hinter : ∀ i ∈ s, IsPreconnected (range (p i) ∩ Uᶜ)) :
    IsPreconnected (U \ (⋃ i ∈ s, (range (p i) ∪ range (w i)))) := by
  apply isPreconnected_sdiff_finset_arcTrees_of_disjoint_inside hU hconn s x
  · intro i hi
    have hp' : Function.Injective (p i).symm := by
      exact (hp i hi).comp unitInterval.symm_involutive.injective
    have hbase : IsFiniteArcTree (x i) (range (p i)) := by
      have ht := IsFiniteArcTree.attach (p i).symm
        (IsFiniteArcTree.singleton : IsFiniteArcTree (x i) {x i}) hp' (by
          rw [Path.symm_range]
          ext z
          simp only [mem_inter_iff, mem_singleton_iff]
          constructor
          · exact And.right
          · intro hz
            subst z
            exact ⟨(p i).source_mem_range, rfl⟩)
      rw [Path.symm_range, Set.union_eq_left.mpr
        (Set.singleton_subset_iff.mpr (p i).source_mem_range)] at ht
      exact ht
    have hw' : Function.Injective (w i).symm :=
      (hw i hi).comp unitInterval.symm_involutive.injective
    have hatt := IsFiniteArcTree.attach (w i).symm hbase hw' (by
      simpa only [Path.symm_range] using hmeet i hi)
    simpa only [Path.symm_range, union_comm] using hatt
  · intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro z ⟨hzi, hzU⟩ hzj
    rcases hzi with hpi | hwi <;> rcases hzj with hpj | hwj
    · exact Set.disjoint_left.mp (hpp i hi j hj hij) ⟨hpi, hzU⟩ hpj
    · exact Set.disjoint_left.mp (hwp j hj i hi hij.symm) hwj hpi
    · exact Set.disjoint_left.mp (hwp i hi j hj hij) hwi hpj
    · exact Set.disjoint_left.mp (hww i hi j hj hij) hwi hwj
  · intro i hi
    have heq : (range (p i) ∪ range (w i)) ∩ Uᶜ = range (p i) ∩ Uᶜ := by
      ext z
      constructor
      · rintro ⟨h | h, hzU⟩
        · exact ⟨h, hzU⟩
        · exact (hzU (hwU i hi h)).elim
      · rintro ⟨h, hzU⟩
        exact ⟨Or.inl h, hzU⟩
    rw [heq]
    exact hinter i hi

/-- Boundary access paths can be joined in a finite arc tree after deleting
finitely many boundary-attached arc trees. -/
theorem exists_rooted_tree_to_boundary_of_arcTrees
    {ι κ : Type*} [DecidableEq κ] {U S : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hconn : IsPreconnected U) (s : Finset ι) (root : ι → ℝ × ℝ)
    (K : ι → Set (ℝ × ℝ))
    (hK : ∀ i ∈ s, IsFiniteArcTree (root i) (K i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (K i ∩ U) (K j))
    (hinter : ∀ i ∈ s, IsPreconnected (K i ∩ Uᶜ))
    (t : Finset κ) {x y : κ → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hp : ∀ i ∈ t, Function.Injective (p i))
    (hpd : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Disjoint (range (p i)) (range (p j)))
    (hinside : ∀ i ∈ t, ∀ a : unitInterval, a ≠ 1 →
      p i a ∈ U \ (⋃ j ∈ s, K j))
    (hout : ∀ i ∈ t, y i ∉ U \ (⋃ j ∈ s, K j))
    (hS : S.Finite) (hps : ∀ i ∈ t, Disjoint (range (p i)) S)
    {r : ℝ × ℝ} (hr : r ∈ ((U \ (⋃ j ∈ s, K j)) \
      (⋃ i ∈ t, range (p i))) \ S) :
    ∃ L : Set (ℝ × ℝ), ∃ u : unitInterval,
      u ≠ 1 ∧ IsFiniteArcTree r L ∧ Disjoint L S ∧
      (∀ i ∈ t, range ((p i).subpath u 1) ⊆ L) ∧
      (∀ i ∈ t, ∃ q : Path r (y i), Function.Injective q ∧ range q ⊆ L) ∧
      L ∩ (U \ (⋃ j ∈ s, K j))ᶜ ⊆ y '' (↑t : Set κ) := by
  have hc : IsCompact (⋃ j ∈ s, K j) :=
    s.isCompact_biUnion (fun j hj => (hK j hj).isCompact)
  obtain ⟨L, u, hu, hL, hLS, htail, hpaths, hboundary, _⟩ :=
    exists_rooted_paths_to_boundary_in_finiteArcTree (hU.sdiff hc.isClosed)
      (isPreconnected_sdiff_finset_arcTrees_of_disjoint_inside hU hconn s root K hK hd hinter)
      t p hp (fun i hi j hj hij => (hpd i hi j hj hij).mono_left inter_subset_left)
      hinside hout hS hps hr t (fun _ hi => hi)
  exact ⟨L, u, hu, hL, hLS, htail, hpaths, hboundary⟩

/-- Charted boundary arcs have disjoint transverse paths whose reversed
interiors avoid every boundary arc and a prescribed point. -/
theorem exists_disjoint_transverse_boundary_access
    {ι : Type*} [DecidableEq ι] {U S : Set (ℝ × ℝ)} (hU : IsOpen U)
    (s : Finset ι) {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (p i) ∩ U) (range (p j)))
    (hinside : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → p i t ∈ U)
    (hS : S.Finite) (hobsS : ∀ i ∈ s, Disjoint (range (p i)) S)
    {r : ℝ × ℝ} (hr : r ∉ ⋃ i ∈ s, range (p i))
    (t : ι → unitInterval) (ht : ∀ i ∈ s, t i ≠ 1)
    (chart : ι → (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (c : ι → ℝ)
    (hvertical : ∀ i ∈ s, ∀ z ∈ range (p i), (chart i z).1 = c i) :
    ∃ b : ι → ℝ × ℝ, ∃ w : ∀ i, Path (p i (t i)) (b i),
      (∀ i ∈ s, Function.Injective (w i) ∧ Disjoint (range (w i)) (S ∪ {r}) ∧
        ∀ a : unitInterval, a ≠ 1 →
          (w i).symm a ∈ U \ (⋃ j ∈ s, range (p j))) ∧
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (range (w i)) (range (w j))) := by
  have hobs : ∀ i ∈ s, Disjoint (range (p i)) (S ∪ {r}) := by
    intro i hi
    apply disjoint_union_right.mpr
    refine ⟨hobsS i hi, ?_⟩
    rw [disjoint_singleton_right]
    intro h
    exact hr (mem_iUnion₂.mpr ⟨i, hi, h⟩)
  obtain ⟨b, w, hw, hww⟩ := exists_disjoint_transverse_paths_to_boundary_arcs
    hU s p hd hinside (hS.union (finite_singleton r)) hobs t ht chart c hvertical
  refine ⟨b, w, ?_, hww⟩
  intro i hi
  obtain ⟨_, hinj, hsub, hmeet⟩ := hw i hi
  have hws : Disjoint (range (w i)) (S ∪ {r}) := by
    apply disjoint_left.mpr
    intro z hz hzS
    exact (hsub hz).2 (Or.inl hzS)
  refine ⟨hinj, hws, ?_⟩
  intro a ha
  have hwr : (w i).symm a ∈ range (w i) := by
    rw [← Path.symm_range (w i)]
    exact ⟨a, rfl⟩
  refine ⟨(hsub hwr).1, ?_⟩
  intro hz
  obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp hz
  by_cases hij : j = i
  · subst j
    have hz_eq : (w i).symm a = p i (t i) :=
      mem_singleton_iff.mp (hmeet ▸ ⟨hwr, hzj⟩)
    have ha' : unitInterval.symm a = 0 := hinj (by simpa using hz_eq)
    have : a = 1 := by
      apply unitInterval.symm_involutive.injective
      simpa using ha'
    exact ha this
  · exact (hsub hwr).2 (Or.inr (mem_iUnion₂.mpr
      ⟨j, Finset.mem_erase.mpr ⟨hij, hj⟩, hzj⟩))

/-- Charted boundary arc points can be joined to a root by a finite arc tree
which retains a transverse path near each marked point. -/
theorem exists_rooted_tree_to_charted_boundary_arcs
    {ι : Type*} [DecidableEq ι] {U S : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hconn : IsPreconnected U) (s : Finset ι) {x y : ι → ℝ × ℝ}
    (p : ∀ i, Path (x i) (y i)) (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (p i) ∩ U) (range (p j)))
    (hinside : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → p i t ∈ U)
    (hinter : ∀ i ∈ s, IsPreconnected (range (p i) ∩ Uᶜ))
    (hS : S.Finite) (hobsS : ∀ i ∈ s, Disjoint (range (p i)) S)
    {r : ℝ × ℝ} (hr : r ∈ (U \ (⋃ i ∈ s, range (p i))) \ S)
    (t : ι → unitInterval) (ht : ∀ i ∈ s, t i ≠ 1)
    (chart : ι → (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (c : ι → ℝ)
    (hvertical : ∀ i ∈ s, ∀ z ∈ range (p i), (chart i z).1 = c i) :
    ∃ b : ι → ℝ × ℝ, ∃ w : ∀ i, Path (p i (t i)) (b i),
    ∃ L : Set (ℝ × ℝ), ∃ u : unitInterval,
      u ≠ 1 ∧ IsFiniteArcTree r L ∧ Disjoint L S ∧
      (∀ i ∈ s, range ((w i).symm.subpath u 1) ⊆ L) ∧
      (∀ i ∈ s, ∃ q : Path r (p i (t i)), Function.Injective q ∧ range q ⊆ L) ∧
      L ∩ (U \ (⋃ j ∈ s, range (p j)))ᶜ ⊆ (fun i => p i (t i)) '' (↑s : Set ι) := by
  obtain ⟨b, w, hw, hww⟩ := exists_disjoint_transverse_boundary_access
    hU s p hd hinside hS hobsS hr.1.2 t ht chart c hvertical
  have htrees : ∀ i ∈ s, IsFiniteArcTree (x i) (range (p i)) := by
    intro i hi
    have hp' : Function.Injective (p i).symm :=
      (hp i hi).comp unitInterval.symm_involutive.injective
    have h := IsFiniteArcTree.attach (p i).symm
      (IsFiniteArcTree.singleton : IsFiniteArcTree (x i) {x i}) hp' (by
        rw [Path.symm_range]
        ext z
        simp only [mem_inter_iff, mem_singleton_iff]
        constructor
        · exact And.right
        · intro hz
          subst z
          exact ⟨(p i).source_mem_range, rfl⟩)
    rw [Path.symm_range, Set.union_eq_left.mpr
      (Set.singleton_subset_iff.mpr (p i).source_mem_range)] at h
    exact h
  have hroot : r ∈ ((U \ (⋃ i ∈ s, range (p i))) \
      (⋃ i ∈ s, range ((w i).symm))) \ S := by
    refine ⟨⟨hr.1, ?_⟩, hr.2⟩
    intro h
    obtain ⟨i, hi, hri⟩ := mem_iUnion₂.mp h
    rw [Path.symm_range] at hri
    exact disjoint_left.mp (hw i hi).2.1 hri (Or.inr (mem_singleton r))
  obtain ⟨L, u, hu, hL, hLS, htail, hpaths, hboundary⟩ :=
    exists_rooted_tree_to_boundary_of_arcTrees hU hconn s x (fun i => range (p i))
      htrees hd hinter s (fun i => (w i).symm)
      (fun i hi => (hw i hi).1.comp unitInterval.symm_involutive.injective)
      (fun i hi j hj hij => by simpa only [Path.symm_range] using hww i hi j hj hij)
      (fun i hi => (hw i hi).2.2)
      (fun i hi h => h.2 (mem_iUnion₂.mpr ⟨i, hi, ⟨t i, rfl⟩⟩))
      hS (fun i hi => by
        rw [Path.symm_range]
        exact (hw i hi).2.1.mono_right subset_union_left) hroot
  exact ⟨b, w, L, u, hu, hL, hLS, htail, hpaths, hboundary⟩

end FiniteAvalanches.Electrical.StatementGeometry
