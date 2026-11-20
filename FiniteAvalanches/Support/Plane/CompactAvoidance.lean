import FiniteAvalanches.Support.Plane.ArcRemoval
import FiniteAvalanches.Support.Plane.GeometricDual
import Mathlib.Topology.Subpath

/-!
# Avoiding compact sets and marked points

A compact nonseparating plane set and finitely many marked points can be avoided
simultaneously by simple polygonal paths in an open connected region.
-/

open Set
open QuantumZipper.CA.Topo MatedCRTHarmonic.Topology

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb

/-- Removing a compact nonseparating set preserves preconnectedness when its
intersection with the complement of the open region is preconnected. -/
theorem isPreconnected_sdiff_nonseparating_compact_of_preconnected_inter_compl {U A : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hA : IsCompact A)
    (hsep : ∀ ⦃a b : ℂ⦄,
      a ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' A →
      b ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' A →
      ¬ Separates (Complex.equivRealProdCLM.symm.toHomeomorph '' A) a b)
    (hinter : IsPreconnected (A ∩ Uᶜ)) : IsPreconnected (U \ A) := by
  let h : (ℝ × ℝ) ≃ₜ ℂ := Complex.equivRealProdCLM.symm.toHomeomorph
  by_cases hne : (U \ A).Nonempty
  · suffices hpath : IsPathConnected (U \ A) from hpath.isConnected.isPreconnected
    apply isPathConnected_iff.mpr
    refine ⟨hne, ?_⟩
    intro a ha b hb
    have himage : ∀ z, z ∈ U \ A → h z ∈ h '' U \ h '' A := by
      intro z hz
      refine ⟨⟨z, hz.1, rfl⟩, ?_⟩
      rintro ⟨w, hw, heq⟩
      exact hz.2 (h.injective heq ▸ hw)
    have hinter' : IsPreconnected ((h '' A) ∩ (h '' U)ᶜ) := by
      have heq : h '' (A ∩ Uᶜ) = (h '' A) ∩ (h '' U)ᶜ := by
        ext z
        constructor
        · rintro ⟨w, ⟨hwA, hwU⟩, rfl⟩
          refine ⟨⟨w, hwA, rfl⟩, ?_⟩
          rintro ⟨v, hv, heq⟩
          exact hwU (h.injective heq ▸ hv)
        · rintro ⟨⟨w, hwA, rfl⟩, hwU⟩
          exact ⟨w, ⟨hwA, fun hw => hwU ⟨w, hw, rfl⟩⟩, rfl⟩
      rw [← heq]
      exact hinter.image h h.continuous.continuousOn
    obtain ⟨p, hp⟩ :=
      exists_path_avoiding_nonseparating_compact_of_preconnected_inter_compl
        (h.isOpenMap _ hU) (hconn.image h h.continuous.continuousOn)
        (hA.image h.continuous) hsep hinter' (himage a ha) (himage b hb)
    let q : Path a b := by
      simpa only [Homeomorph.symm_apply_apply] using p.map h.symm.continuous
    refine ⟨q, ?_⟩
    intro t
    have ht := hp ⟨t, rfl⟩
    refine ⟨?_, ?_⟩
    · change h.symm (p t) ∈ U
      obtain ⟨w, hw, heq⟩ := ht.1
      simpa only [← heq, Homeomorph.symm_apply_apply] using hw
    · change h.symm (p t) ∉ A
      intro hmem
      exact ht.2 ⟨h.symm (p t), hmem, h.apply_symm_apply _⟩
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact isPreconnected_empty

/-- Removing a compact nonseparating set from a containing open preconnected region
preserves preconnectedness. -/
theorem isPreconnected_sdiff_nonseparating_compact {U A : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hA : IsCompact A)
    (hsep : ∀ ⦃a b : ℂ⦄,
      a ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' A →
      b ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' A →
      ¬ Separates (Complex.equivRealProdCLM.symm.toHomeomorph '' A) a b)
    (hAU : A ⊆ U) : IsPreconnected (U \ A) := by
  let h : (ℝ × ℝ) ≃ₜ ℂ := Complex.equivRealProdCLM.symm.toHomeomorph
  by_cases hne : (U \ A).Nonempty
  · suffices hpath : IsPathConnected (U \ A) from hpath.isConnected.isPreconnected
    apply isPathConnected_iff.mpr
    refine ⟨hne, ?_⟩
    intro a ha b hb
    have himage : ∀ z, z ∈ U \ A → h z ∈ h '' U \ h '' A := by
      intro z hz
      refine ⟨⟨z, hz.1, rfl⟩, ?_⟩
      rintro ⟨w, hw, heq⟩
      exact hz.2 (h.injective heq ▸ hw)
    obtain ⟨p, hp⟩ := exists_path_avoiding_nonseparating_compact
      (h.isOpenMap _ hU) (hconn.image h h.continuous.continuousOn)
      (hA.image h.continuous) hsep (Set.image_mono hAU) (himage a ha) (himage b hb)
    let q : Path a b := by
      simpa only [Homeomorph.symm_apply_apply] using p.map h.symm.continuous
    refine ⟨q, ?_⟩
    intro t
    have ht := hp ⟨t, rfl⟩
    refine ⟨?_, ?_⟩
    · change h.symm (p t) ∈ U
      obtain ⟨w, hw, heq⟩ := ht.1
      simpa only [← heq, Homeomorph.symm_apply_apply] using hw
    · change h.symm (p t) ∉ A
      intro hmem
      exact ht.2 ⟨h.symm (p t), hmem, h.apply_symm_apply _⟩
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact isPreconnected_empty

/-- A compact nonseparating obstacle and finitely many points can be avoided by a
simple polygonal path. -/
theorem exists_injective_polygonal_path_avoiding_compact_finite
    {U A S : Set (ℝ × ℝ)} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hA : IsCompact A)
    (hsep : ∀ ⦃a b : ℂ⦄,
      a ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' A →
      b ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' A →
      ¬ Separates (Complex.equivRealProdCLM.symm.toHomeomorph '' A) a b)
    (hAU : A ⊆ U) (hS : S.Finite) {a b : ℝ × ℝ}
    (ha : a ∈ (U \ A) \ S) (hb : b ∈ (U \ A) \ S) (hab : a ≠ b) :
    ∃ q : Path a b, ∃ vs : List (ℝ × ℝ),
      LatticeProb.Topology.IsSimplePolygonalChain vs ∧ Function.Injective q ∧
      range q = LatticeProb.Topology.polygonalChain vs ∧ range q ⊆ (U \ A) \ S := by
  have hopen : IsOpen (U \ A) := hU.sdiff hA.isClosed
  obtain ⟨vs, hv, hsub, hhead, hlast⟩ :=
    LatticeProb.Topology.exists_polygonal_chain_of_isPreconnected
      (hopen.sdiff hS.isClosed)
      (isPreconnected_sdiff_finite hopen
        (isPreconnected_sdiff_nonseparating_compact hU hconn hA hsep hAU) hS) ha hb
  have hvne : vs.head hv ≠ vs.getLast hv := by simpa only [hhead, hlast] using hab
  obtain ⟨us, hu, hs, hh, hl, hsub', hinj, hrange⟩ :=
    LatticeProb.Topology.exists_injective_polygonal_arc vs hv hvne
  let q := (LatticeProb.Topology.polygonalChainPath us hu).cast
    (hh.trans hhead).symm (hl.trans hlast).symm
  exact ⟨q, us, hs, hinj, hrange, hrange ▸ hsub'.trans hsub⟩

/-- First hitting time of a closed set, following `Topology.Length.InternalOps`. -/
private theorem exists_first_hit {X : Type*} [TopologicalSpace X] {P : ℝ → X}
    {a b : ℝ} (hP : ContinuousOn P (Icc a b)) {K : Set X} (hK : IsClosed K)
    (hne : ∃ t ∈ Icc a b, P t ∈ K) :
    ∃ t ∈ Icc a b, P t ∈ K ∧ ∀ s ∈ Ico a t, P s ∉ K := by
  let S := Icc a b ∩ P ⁻¹' K
  have hS : IsClosed S := hP.preimage_isClosed_of_isClosed isClosed_Icc hK
  have hSne : S.Nonempty := let ⟨t, ht, htK⟩ := hne; ⟨t, ht, htK⟩
  have hbdd : BddBelow S := ⟨a, fun t ht => ht.1.1⟩
  have hmem := hS.csInf_mem hSne hbdd
  refine ⟨sInf S, hmem.1, hmem.2, fun s hs hsK => ?_⟩
  have hle : sInf S ≤ s := csInf_le hbdd ⟨⟨hs.1, hs.2.le.trans hmem.1.2⟩, hsK⟩
  exact (not_lt_of_ge hle) hs.2

/-- An injective path ending in a closed set has an initial injective subpath
meeting that set only at its endpoint. -/
theorem exists_initial_path_first_hit_with_subpath {X : Type*} [TopologicalSpace X]
    {a b : X} (p : Path a b) (hp : Function.Injective p)
    {K : Set X} (hK : IsClosed K) (ha : a ∉ K) (hb : b ∈ K) :
    ∃ z ∈ K, ∃ q : Path a z, Function.Injective q ∧ range q ⊆ range p ∧
      range q ∩ K = {z} ∧
      ∃ t : unitInterval, t ≠ 0 ∧ range (p.subpath 0 t) = range q := by
  obtain ⟨t, ht, htK, hfirst⟩ := exists_first_hit
    p.continuous_extend.continuousOn hK
    (show ∃ t ∈ Set.Icc (0 : ℝ) 1, p.extend t ∈ K from
      ⟨1, ⟨by norm_num, le_rfl⟩, by simpa only [Path.extend_one] using hb⟩)
  let T : unitInterval := ⟨t, ht⟩
  have hT : p T ∈ K := by simpa only [Path.extend_apply _ ht] using htK
  have htpos : 0 < t := by
    have hne : t ≠ 0 := by
      intro heq
      apply ha
      simpa only [heq, Path.extend_zero] using htK
    exact lt_of_le_of_ne ht.1 (Ne.symm hne)
  let q : Path a (p T) := (p.subpath 0 T).cast p.source.symm rfl
  refine ⟨p T, hT, q, ?_, ?_, ?_, ⟨T, ?_, rfl⟩⟩
  · intro s u hsu
    apply Subtype.ext
    have hh := hp hsu
    have hv := congrArg Subtype.val hh
    simp only [Set.Icc.coe_convexComb] at hv
    change (1 - (s : ℝ)) * 0 + (s : ℝ) * t =
      (1 - (u : ℝ)) * 0 + (u : ℝ) * t at hv
    simp only [mul_zero, zero_add] at hv
    exact mul_right_cancel₀ (ne_of_gt htpos) hv
  · intro z hz
    change z ∈ range (p.subpath 0 T) at hz
    rw [Path.range_subpath_of_le _ _ _ (by exact bot_le)] at hz
    obtain ⟨s, _, rfl⟩ := hz
    exact ⟨s, rfl⟩
  · ext z
    simp only [mem_inter_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hz, hzK⟩
      change z ∈ range (p.subpath 0 T) at hz
      rw [Path.range_subpath_of_le _ _ _ (by exact bot_le)] at hz
      obtain ⟨s, hs, rfl⟩ := hz
      have hst : s = T := by
        by_contra hne
        have hslt : (s : ℝ) < t := lt_of_le_of_ne hs.2 (fun heq => hne (Subtype.ext heq))
        have hnot := hfirst s ⟨s.property.1, hslt⟩
        exact hnot (by simpa only [Path.extend_apply _ s.property] using hzK)
      rw [hst]
    · intro hz
      subst z
      exact ⟨q.target_mem_range, hT⟩
  · intro h
    have : t = 0 := congrArg Subtype.val h
    linarith

/-- An injective path ending in a closed set has an initial injective subpath
meeting that set only at its endpoint. -/
theorem exists_initial_path_first_hit {X : Type*} [TopologicalSpace X]
    {a b : X} (p : Path a b) (hp : Function.Injective p)
    {K : Set X} (hK : IsClosed K) (ha : a ∉ K) (hb : b ∈ K) :
    ∃ z ∈ K, ∃ q : Path a z, Function.Injective q ∧ range q ⊆ range p ∧
      range q ∩ K = {z} := by
  obtain ⟨z, hz, q, hq, hsub, hinter, _⟩ :=
    exists_initial_path_first_hit_with_subpath p hp hK ha hb
  exact ⟨z, hz, q, hq, hsub, hinter⟩

/-- A point can be joined to a closed set by a simple path that avoids finitely
many marked points and meets the set only at its endpoint. -/
theorem exists_path_to_closed_set_avoiding_finite {U A S : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hA : IsClosed A) (hS : S.Finite)
    {x y : ℝ × ℝ} (hx : x ∈ (U \ S) \ A) (hy : y ∈ (U \ S) ∩ A) :
    ∃ z ∈ A, ∃ q : Path x z, Function.Injective q ∧ range q ⊆ U \ S ∧
      range q ∩ A = {z} := by
  have hne : x ≠ y := fun h => hx.2 (h ▸ hy.2)
  obtain ⟨vs, hv, hsub, hhead, hlast⟩ :=
    LatticeProb.Topology.exists_polygonal_chain_of_isPreconnected
      (hU.sdiff hS.isClosed) (isPreconnected_sdiff_finite hU hconn hS) hx.1 hy.1
  have hvne : vs.head hv ≠ vs.getLast hv := by simpa only [hhead, hlast] using hne
  obtain ⟨us, hu, _, hh, hl, hsub', hinj, hrange⟩ :=
    LatticeProb.Topology.exists_injective_polygonal_arc vs hv hvne
  let p := (LatticeProb.Topology.polygonalChainPath us hu).cast
    (hh.trans hhead).symm (hl.trans hlast).symm
  have hp : range p ⊆ U \ S := hrange ▸ hsub'.trans hsub
  obtain ⟨z, hz, q, hqinj, hqsub, hqinter⟩ :=
    exists_initial_path_first_hit p hinj hA hx.2 hy.2
  exact ⟨z, hz, q, hqinj, hqsub.trans hp, hqinter⟩

/-- Adding an injective arc along a preconnected intersection preserves compact
nonseparation in the plane. -/
theorem not_separates_image_union_path {A : Set (ℝ × ℝ)} (hA : IsCompact A)
    (hsep : ∀ ⦃a b : ℂ⦄,
      a ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' A →
      b ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' A →
      ¬ Separates (Complex.equivRealProdCLM.symm.toHomeomorph '' A) a b)
    {x y : ℝ × ℝ} (p : Path x y) (hp : Function.Injective p)
    (hinter : IsPreconnected (range p ∩ A)) :
    ∀ ⦃a b : ℂ⦄,
      a ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' (range p ∪ A) →
      b ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' (range p ∪ A) →
      ¬ Separates (Complex.equivRealProdCLM.symm.toHomeomorph '' (range p ∪ A)) a b := by
  let h : (ℝ × ℝ) ≃ₜ ℂ := Complex.equivRealProdCLM.symm.toHomeomorph
  let q := p.map h.continuous
  have hrange : range q = h '' range p := by
    ext z
    simp only [q, Path.map_coe, Function.comp_apply, mem_range, mem_image]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨p t, ⟨t, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
  have hinter' : IsPreconnected (range q ∩ h '' A) := by
    rw [hrange, ← Set.image_inter h.injective]
    exact hinter.image h h.continuous.continuousOn
  intro a b ha hb
  rw [Set.image_union] at ha hb ⊢
  rw [← hrange] at ha hb ⊢
  exact not_separates_union_arc (isArcSet_range q (h.injective.comp hp))
    (hA.image h.continuous) hinter' hsep ha hb

/-- A marked point can be attached to a compact nonseparating set while preserving
nonseparation and avoiding a finite set. -/
theorem exists_nonseparating_attachment {U A S : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hA : IsCompact A)
    (hsep : ∀ ⦃a b : ℂ⦄,
      a ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' A →
      b ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' A →
      ¬ Separates (Complex.equivRealProdCLM.symm.toHomeomorph '' A) a b)
    (hS : S.Finite) {x y : ℝ × ℝ} (hx : x ∈ (U \ S) \ A)
    (hy : y ∈ (U \ S) ∩ A) :
    ∃ z ∈ A, ∃ p : Path x z, Function.Injective p ∧ range p ⊆ U \ S ∧
      range p ∩ A = {z} ∧
      ∀ ⦃a b : ℂ⦄,
        a ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' (range p ∪ A) →
        b ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' (range p ∪ A) →
        ¬ Separates (Complex.equivRealProdCLM.symm.toHomeomorph '' (range p ∪ A)) a b := by
  obtain ⟨z, hz, p, hp, hsub, hinter⟩ :=
    exists_path_to_closed_set_avoiding_finite hU hconn hA.isClosed hS hx hy
  refine ⟨z, hz, p, hp, hsub, hinter, ?_⟩
  apply not_separates_image_union_path hA hsep p hp
  rw [hinter]
  exact isPreconnected_singleton

/-- A singleton does not separate the plane. -/
theorem not_separates_image_singleton (x : ℝ × ℝ) :
    ∀ ⦃a b : ℂ⦄,
      a ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' ({x} : Set (ℝ × ℝ)) →
      b ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' ({x} : Set (ℝ × ℝ)) →
      ¬ Separates (Complex.equivRealProdCLM.symm.toHomeomorph '' ({x} : Set (ℝ × ℝ))) a b := by
  let h : (ℝ × ℝ) ≃ₜ ℂ := Complex.equivRealProdCLM.symm.toHomeomorph
  intro a b ha hb
  have hc : IsPreconnected ((Set.univ : Set (ℝ × ℝ)) \ {x}) :=
    isPreconnected_sdiff_finite isOpen_univ isPreconnected_univ (Set.finite_singleton x)
  have ha' : h.symm a ∈ (Set.univ : Set (ℝ × ℝ)) \ {x} := by
    refine ⟨Set.mem_univ _, ?_⟩
    intro hx
    exact ha ⟨h.symm a, hx, h.apply_symm_apply a⟩
  have hb' : h.symm b ∈ (Set.univ : Set (ℝ × ℝ)) \ {x} := by
    refine ⟨Set.mem_univ _, ?_⟩
    intro hx
    exact hb ⟨h.symm b, hx, h.apply_symm_apply b⟩
  have hpath : IsPathConnected ((Set.univ : Set (ℝ × ℝ)) \ {x}) :=
    (isOpen_univ.sdiff isClosed_singleton).isConnected_iff_isPathConnected.mp
      ⟨⟨_, ha'⟩, hc⟩
  obtain ⟨p, hp⟩ := hpath.joinedIn _ ha' _ hb'
  let q : Path a b := by
    simpa only [Homeomorph.apply_symm_apply] using p.map h.continuous
  intro hsep
  obtain ⟨t, ht⟩ := hsep q
  obtain ⟨w, hw, heq⟩ := ht
  have heq' : w = p t := h.injective heq
  exact (hp t).2 (heq' ▸ hw)

/-- A finite planar arc tree is built from one root by attaching simple arcs at
one point at a time. -/
inductive IsFiniteArcTree (r : ℝ × ℝ) : Set (ℝ × ℝ) → Prop
  | singleton : IsFiniteArcTree r {r}
  | attach {K : Set (ℝ × ℝ)} {x z : ℝ × ℝ} (p : Path x z)
      (hK : IsFiniteArcTree r K) (hp : Function.Injective p)
      (hinter : range p ∩ K = {z}) : IsFiniteArcTree r (range p ∪ K)

/-- A finite arc tree is compact. -/
theorem IsFiniteArcTree.isCompact {r : ℝ × ℝ} {K : Set (ℝ × ℝ)}
    (hK : IsFiniteArcTree r K) : IsCompact K := by
  induction hK with
  | singleton => exact isCompact_singleton
  | attach p _ _ _ ih => exact (isCompact_range p.continuous).union ih

/-- A finite arc tree is path connected. -/
theorem IsFiniteArcTree.isPathConnected {r : ℝ × ℝ} {K : Set (ℝ × ℝ)}
    (hK : IsFiniteArcTree r K) : IsPathConnected K := by
  induction hK with
  | singleton => exact isPathConnected_singleton r
  | @attach K x z p hK hp hinter ih =>
      let : PathConnectedSpace unitInterval := isPathConnected_iff_pathConnectedSpace.mp
        ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, by norm_num⟩)
      apply (isPathConnected_range p.continuous).union ih
      rw [hinter]
      exact Set.singleton_nonempty z

/-- A finite arc tree does not separate the plane. -/
theorem IsFiniteArcTree.not_separates {r : ℝ × ℝ} {K : Set (ℝ × ℝ)}
    (hK : IsFiniteArcTree r K) :
    ∀ ⦃a b : ℂ⦄,
      a ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' K →
      b ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' K →
      ¬ Separates (Complex.equivRealProdCLM.symm.toHomeomorph '' K) a b := by
  induction hK with
  | singleton => exact not_separates_image_singleton r
  | attach p hK hp hinter ih =>
      apply not_separates_image_union_path hK.isCompact ih p hp
      rw [hinter]
      exact isPreconnected_singleton

/-- Finitely many points of an open connected plane region lie in a compact connected
nonseparating finite arc tree avoiding a prescribed finite set. -/
theorem exists_compact_nonseparating_of_finite {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U) (F : Finset (ℝ × ℝ)) :
    ∀ (T : Set (ℝ × ℝ)) (_hT : T.Finite) (r : ℝ × ℝ),
      r ∈ U \ T → r ∉ F → (∀ x ∈ F, x ∈ U \ T) →
      ∃ K : Set (ℝ × ℝ), IsFiniteArcTree r K ∧ IsCompact K ∧ IsPreconnected K ∧
        K ⊆ U \ T ∧ r ∈ K ∧ (∀ x ∈ F, x ∈ K) ∧
        ∀ ⦃a b : ℂ⦄,
          a ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' K →
          b ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' K →
          ¬ Separates (Complex.equivRealProdCLM.symm.toHomeomorph '' K) a b := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      intro T _hT r hr hrF hF
      refine ⟨{r}, IsFiniteArcTree.singleton, isCompact_singleton,
        isPreconnected_singleton, ?_, by simp, ?_, not_separates_image_singleton r⟩
      · simpa only [singleton_subset_iff] using hr
      · simp
  | @insert x F hxF ih =>
      intro T hT r hr hrF hF
      have hx : x ∈ U \ T := hF x (Finset.mem_insert_self x F)
      have hrx : r ≠ x := fun heq => hrF (heq ▸ Finset.mem_insert_self x F)
      have hrF' : r ∉ F := fun h => hrF (Finset.mem_insert_of_mem h)
      have hr' : r ∈ U \ (insert x T) := ⟨hr.1, by simpa using ⟨hrx, hr.2⟩⟩
      have hF' : ∀ y ∈ F, y ∈ U \ (insert x T) := by
        intro y hy
        have hy' := hF y (Finset.mem_insert_of_mem hy)
        refine ⟨hy'.1, ?_⟩
        simp only [mem_insert_iff, not_or]
        exact ⟨fun h => hxF (h ▸ hy), hy'.2⟩
      obtain ⟨K, hKtree, hK, hKconn, hKsub, hrK, hFK, hKsep⟩ :=
        ih (insert x T) (hT.insert x) r hr' hrF' hF'
      have hxK : x ∉ K := fun h => (hKsub h).2 (Set.mem_insert x T)
      obtain ⟨z, hz, p, hp, hpU, hpK, hpsep⟩ :=
        exists_nonseparating_attachment hU hconn hK hKsep hT
          (show x ∈ (U \ T) \ K from ⟨hx, hxK⟩)
          (show r ∈ (U \ T) ∩ K from ⟨hr, hrK⟩)
      refine ⟨range p ∪ K, IsFiniteArcTree.attach p hKtree hp hpK,
        (isCompact_range p.continuous).union hK, ?_, ?_,
        Or.inr hrK, ?_, hpsep⟩
      · exact IsPreconnected.union z p.target_mem_range hz
          (isPreconnected_range p.continuous) hKconn
      · exact union_subset hpU (fun y hy => ⟨(hKsub hy).1, fun hyT =>
          (hKsub hy).2 (Set.mem_insert_of_mem x hyT)⟩)
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact Or.inl p.source_mem_range
        · exact Or.inr (hFK y hy)

/-- A finite union of pairwise disjoint simple arcs does not separate the plane. -/
theorem not_separates_image_finset_paths {ι : Type*} (s : Finset ι)
    {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (range (p i)) (range (p j))) :
    ∀ ⦃a b : ℂ⦄,
      a ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' (⋃ i ∈ s, range (p i)) →
      b ∉ Complex.equivRealProdCLM.symm.toHomeomorph '' (⋃ i ∈ s, range (p i)) →
      ¬ Separates (Complex.equivRealProdCLM.symm.toHomeomorph ''
        (⋃ i ∈ s, range (p i))) a b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro a b _ _ hsep
      obtain ⟨q, _⟩ := (isPathConnected_univ : IsPathConnected (univ : Set ℂ)).joinedIn
        a (mem_univ a) b (mem_univ b)
      obtain ⟨t, ht⟩ := hsep q
      simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, image_empty,
        notMem_empty] at ht
  | @insert i s hi ih =>
      have hp' : ∀ j ∈ s, Function.Injective (p j) :=
        fun j hj => hp j (Finset.mem_insert_of_mem hj)
      have hd' : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → Disjoint (range (p j)) (range (p k)) :=
        fun j hj k hk hne => hd j (Finset.mem_insert_of_mem hj)
          k (Finset.mem_insert_of_mem hk) hne
      have hc : IsCompact (⋃ j ∈ s, range (p j)) :=
        s.isCompact_biUnion (fun j _ => isCompact_range (p j).continuous)
      have hinter : range (p i) ∩ (⋃ j ∈ s, range (p j)) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro z hz
        obtain ⟨j, hj, hzj⟩ := Set.mem_iUnion₂.mp hz.2
        exact Set.disjoint_left.mp (hd i (Finset.mem_insert_self i s) j
          (Finset.mem_insert_of_mem hj) (fun h => hi (h ▸ hj))) hz.1 hzj
      have hsep := not_separates_image_union_path hc (ih hp' hd') (p i)
        (hp i (Finset.mem_insert_self i s)) (hinter ▸ isPreconnected_empty)
      have hunion : (⋃ j ∈ insert i s, range (p j)) =
          range (p i) ∪ (⋃ j ∈ s, range (p j)) := by
        ext z
        simp only [mem_iUnion, Finset.mem_insert, mem_union]
        constructor
        · rintro ⟨j, (rfl | hj), hz⟩
          · exact Or.inl hz
          · exact Or.inr ⟨j, hj, hz⟩
        · rintro (hz | ⟨j, hj, hz⟩)
          · exact ⟨i, Or.inl rfl, hz⟩
          · exact ⟨j, Or.inr hj, hz⟩
      rw [hunion]
      exact hsep

/-- Removing finitely many pairwise disjoint simple arcs contained in an open
connected plane region preserves preconnectedness. -/
theorem isPreconnected_sdiff_finset_paths {ι : Type*} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U) (s : Finset ι)
    {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (range (p i)) (range (p j)))
    (hsub : ∀ i ∈ s, range (p i) ⊆ U) :
    IsPreconnected (U \ (⋃ i ∈ s, range (p i))) := by
  apply isPreconnected_sdiff_nonseparating_compact hU hconn
    (s.isCompact_biUnion fun i _ => isCompact_range (p i).continuous)
    (not_separates_image_finset_paths s p hp hd)
  exact iUnion₂_subset hsub

/-- Removing finitely many disjoint simple arcs preserves preconnectedness if
 each arc meets the complement of the open region in a preconnected set. -/
theorem isPreconnected_sdiff_finset_paths_of_preconnected_inter_compl
    {ι : Type*} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hconn : IsPreconnected U)
    (s : Finset ι) {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (range (p i)) (range (p j)))
    (hinter : ∀ i ∈ s, IsPreconnected (range (p i) ∩ Uᶜ)) :
    IsPreconnected (U \ (⋃ i ∈ s, range (p i))) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hconn
  | @insert i s hi ih =>
      have hc : IsCompact (⋃ j ∈ s, range (p j)) :=
        s.isCompact_biUnion (fun j _ => isCompact_range (p j).continuous)
      have hprev := ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))
        (fun j hj k hk hne => hd j (Finset.mem_insert_of_mem hj)
          k (Finset.mem_insert_of_mem hk) hne)
        (fun j hj => hinter j (Finset.mem_insert_of_mem hj))
      have hdisj : Disjoint (range (p i)) (⋃ j ∈ s, range (p j)) := by
        apply Set.disjoint_left.mpr
        intro z hzi hzs
        obtain ⟨j, hj, hzj⟩ := Set.mem_iUnion₂.mp hzs
        exact Set.disjoint_left.mp (hd i (Finset.mem_insert_self i s) j
          (Finset.mem_insert_of_mem hj) (fun h => hi (h ▸ hj))) hzi hzj
      have hinter' : range (p i) ∩ (U \ (⋃ j ∈ s, range (p j)))ᶜ =
          range (p i) ∩ Uᶜ := by
        ext z
        simp only [mem_inter_iff, mem_compl_iff, mem_sdiff]
        constructor
        · rintro ⟨hzi, hn⟩
          refine ⟨hzi, fun hzU => hn ⟨hzU, ?_⟩⟩
          exact fun hz => Set.disjoint_left.mp hdisj hzi hz
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
      have heq : U \ (⋃ j ∈ insert i s, range (p j)) =
          (U \ (⋃ j ∈ s, range (p j))) \ range (p i) := by
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
      rw [heq]
      exact hnew

/-- Points in an open connected region can be joined by a finite arc tree
avoiding finitely many disjoint simple arcs and finitely many marked points. -/
theorem exists_finiteArcTree_avoiding_finset_paths {ι : Type*} {U T : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U) (s : Finset ι)
    {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (range (p i)) (range (p j)))
    (hsub : ∀ i ∈ s, range (p i) ⊆ U) (hT : T.Finite)
    (F : Finset (ℝ × ℝ)) (r : ℝ × ℝ)
    (hr : r ∈ (U \ (⋃ i ∈ s, range (p i))) \ T) (hrF : r ∉ F)
    (hF : ∀ z ∈ F, z ∈ (U \ (⋃ i ∈ s, range (p i))) \ T) :
    ∃ K : Set (ℝ × ℝ), IsFiniteArcTree r K ∧
      K ⊆ (U \ (⋃ i ∈ s, range (p i))) \ T ∧ r ∈ K ∧
      ∀ z ∈ F, z ∈ K := by
  have hc : IsCompact (⋃ i ∈ s, range (p i)) :=
    s.isCompact_biUnion (fun i _ => isCompact_range (p i).continuous)
  obtain ⟨K, htree, _, _, hK, hrK, hFK, _⟩ :=
    exists_compact_nonseparating_of_finite (hU.sdiff hc.isClosed)
      (isPreconnected_sdiff_finset_paths hU hconn s p hp hd hsub) F T hT r hr hrF hF
  exact ⟨K, htree, hK, hrK, hFK⟩

end FiniteAvalanches.Electrical.StatementGeometry

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb

open Source BSST

/-- Finite sets of points in each face lie in pairwise disjoint arc trees, while
avoiding prescribed arcs and marked points in their respective faces. -/
theorem exists_face_finiteArcTrees_avoiding_paths
    {V E : Type} {ι : Type*} [Fintype V] [Fintype E] {J : CopiedGraph V E}
    (D : Drawing J) (s : Face D → Finset ι)
    {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hp : ∀ F i, i ∈ s F → Function.Injective (p i))
    (hd : ∀ F i, i ∈ s F → ∀ j, j ∈ s F → i ≠ j →
      Disjoint (range (p i)) (range (p j)))
    (hsub : ∀ F i, i ∈ s F → range (p i) ⊆ faceRegion D F)
    (T : Face D → Set (ℝ × ℝ)) (hT : ∀ F, (T F).Finite)
    (A : Face D → Finset (ℝ × ℝ)) (r : Face D → ℝ × ℝ)
    (hr : ∀ F, r F ∈ (faceRegion D F \ (⋃ i ∈ s F, range (p i))) \ T F)
    (hrA : ∀ F, r F ∉ A F)
    (hA : ∀ F z, z ∈ A F →
      z ∈ (faceRegion D F \ (⋃ i ∈ s F, range (p i))) \ T F) :
    ∃ K : Face D → Set (ℝ × ℝ),
      (∀ F, IsFiniteArcTree (r F) (K F) ∧
        K F ⊆ (faceRegion D F \ (⋃ i ∈ s F, range (p i))) \ T F ∧
        r F ∈ K F ∧ ∀ z ∈ A F, z ∈ K F) ∧
      ∀ F G, F ≠ G → Disjoint (K F) (K G) := by
  have hex : ∀ F, ∃ K : Set (ℝ × ℝ), IsFiniteArcTree (r F) K ∧
      K ⊆ (faceRegion D F \ (⋃ i ∈ s F, range (p i))) \ T F ∧
      r F ∈ K ∧ ∀ z ∈ A F, z ∈ K := by
    intro F
    exact exists_finiteArcTree_avoiding_finset_paths (punctured_faceRegion_isOpen D F)
      (faceRegion_isConnected D F).isPreconnected (s F) p (hp F) (hd F) (hsub F)
      (hT F) (A F) (r F) (hr F) (hrA F) (hA F)
  choose K hK using hex
  refine ⟨K, hK, ?_⟩
  intro F G hFG
  exact (faceRegion_disjoint D hFG).mono
    (fun z hz => ((hK F).2.1 hz).1.1)
    (fun z hz => ((hK G).2.1 hz).1.1)


/-- If each face has a prescribed point, roots for avoiding arc trees can be
chosen simultaneously in the respective faces. -/
theorem exists_rooted_face_finiteArcTrees_avoiding_paths
    {V E : Type} {ι : Type*} [Fintype V] [Fintype E] {J : CopiedGraph V E}
    (D : Drawing J) (s : Face D → Finset ι)
    {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hp : ∀ F i, i ∈ s F → Function.Injective (p i))
    (hd : ∀ F i, i ∈ s F → ∀ j, j ∈ s F → i ≠ j →
      Disjoint (range (p i)) (range (p j)))
    (hsub : ∀ F i, i ∈ s F → range (p i) ⊆ faceRegion D F)
    (T : Face D → Set (ℝ × ℝ)) (hT : ∀ F, (T F).Finite)
    (A : Face D → Finset (ℝ × ℝ)) (hne : ∀ F, (A F).Nonempty)
    (hA : ∀ F z, z ∈ A F →
      z ∈ (faceRegion D F \ (⋃ i ∈ s F, range (p i))) \ T F) :
    ∃ r : Face D → ℝ × ℝ, ∃ K : Face D → Set (ℝ × ℝ),
      (∀ F, IsFiniteArcTree (r F) (K F) ∧
        K F ⊆ (faceRegion D F \ (⋃ i ∈ s F, range (p i))) \ T F ∧
        r F ∈ K F ∧ ∀ z ∈ A F, z ∈ K F) ∧
      ∀ F G, F ≠ G → Disjoint (K F) (K G) := by
  have hroot : ∀ F, ∃ r : ℝ × ℝ,
      r ∈ (faceRegion D F \ (⋃ i ∈ s F, range (p i))) \ T F ∧ r ∉ A F := by
    intro F
    have hc : IsCompact (⋃ i ∈ s F, range (p i)) :=
      (s F).isCompact_biUnion (fun i _ => isCompact_range (p i).continuous)
    have hopen : IsOpen (faceRegion D F \ (⋃ i ∈ s F, range (p i))) :=
      (punctured_faceRegion_isOpen D F).sdiff hc.isClosed
    obtain ⟨z, hz⟩ := hne F
    have hnonempty : (faceRegion D F \ (⋃ i ∈ s F, range (p i))).Nonempty :=
      ⟨z, (hA F z hz).1⟩
    have hfinite : (T F ∪ (A F : Set (ℝ × ℝ))).Finite :=
      (hT F).union (A F).finite_toSet
    have hdense : Dense (T F ∪ (A F : Set (ℝ × ℝ)))ᶜ := by
      rw [Set.compl_eq_univ_sdiff]
      exact dense_univ.sdiff_finite hfinite
    obtain ⟨r, hr, havoid⟩ := hdense.inter_open_nonempty _ hopen hnonempty
    exact ⟨r, ⟨hr, fun ht => havoid (Or.inl ht)⟩, fun ht => havoid (Or.inr ht)⟩
  choose r hr hrA using hroot
  obtain ⟨K, hK, hdisj⟩ :=
    exists_face_finiteArcTrees_avoiding_paths D s p hp hd hsub T hT A r hr hrA hA
  exact ⟨r, K, hK, hdisj⟩

end FiniteAvalanches.Electrical.StatementGeometry
