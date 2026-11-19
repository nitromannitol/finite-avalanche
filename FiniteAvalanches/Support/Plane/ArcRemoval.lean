import FiniteAvalanches.Support.Plane.PlanarCore
import LatticeProb.Topology.PolygonalArc

/-!
Ported from Lattice-Probability `LatticeProb/Topology/PlaneGraph/ArcRemoval.lean` at commit `ba2b67f3`.

# Removing an arc from an open plane region

An arc contained in an open connected plane region does not disconnect the region.
-/

open Set Metric
open QuantumZipper.CA.Topo MatedCRTHarmonic.Topology

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb

/-- A compact nonseparating set whose intersection with the complement of an open
connected region is preconnected can be avoided within the region. -/
theorem exists_path_avoiding_nonseparating_compact_of_preconnected_inter_compl
    {U A : Set ℂ} (hU : IsOpen U)
    (hconn : IsPreconnected U) (hA : IsCompact A)
    (hsep : ∀ ⦃a b : ℂ⦄, a ∉ A → b ∉ A → ¬ Separates A a b)
    (hinter : IsPreconnected (A ∩ Uᶜ))
    {a b : ℂ} (ha : a ∈ U \ A) (hb : b ∈ U \ A) :
    ∃ p : Path a b, range p ⊆ U \ A := by
  have hUpath : IsPathConnected U :=
    hU.isConnected_iff_isPathConnected.mp ⟨⟨a, ha.1⟩, hconn⟩
  obtain ⟨γ, hγ⟩ := hUpath.joinedIn a ha.1 b hb.1
  have hcompact : IsCompact (A ∪ range γ) := hA.union (isCompact_range γ.continuous)
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : ℂ)).mp hcompact.isBounded
  let K : Set ℂ := (closedBall 0 R \ U) ∪ sphere 0 R
  have hKcompact : IsCompact K := by
    apply (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
    · exact (isClosed_closedBall.sdiff hU).union isClosed_sphere
    · exact union_subset sdiff_subset sphere_subset_closedBall
  have hAK : A ∩ K = A ∩ Uᶜ := by
    ext z
    constructor
    · rintro ⟨hzA, hzK⟩
      rcases hzK with ⟨_, hzU⟩ | hzSphere
      · exact ⟨hzA, hzU⟩
      · exact (Metric.sphere_disjoint_ball.le_bot ⟨hzSphere, hR (Or.inl hzA)⟩).elim
    · rintro ⟨hzA, hzU⟩
      exact ⟨hzA, Or.inl ⟨ball_subset_closedBall (hR (Or.inl hzA)), hzU⟩⟩
  have hγK : ∀ t, γ t ∉ K := by
    intro t ht
    have htball : γ t ∈ ball (0 : ℂ) R := hR (Or.inr ⟨t, rfl⟩)
    rcases ht with ⟨_, htU⟩ | htsphere
    · exact htU (hγ t)
    · exact Metric.sphere_disjoint_ball.le_bot ⟨htsphere, htball⟩
  have haK : a ∉ K := by simpa only [γ.source] using hγK 0
  have hbK : b ∉ K := by simpa only [γ.target] using hγK 1
  have hcompA : b ∈ connectedComponentIn Aᶜ a := by
    by_contra h
    exact hsep ha.2 hb.2 ((separates_iff_not_mem_connectedComponentIn_compl hA.isClosed).mpr h)
  have hcompK : b ∈ connectedComponentIn Kᶜ a :=
    (mem_connectedComponentIn_compl_iff_exists_path_avoiding hKcompact.isClosed).mpr ⟨γ, hγK⟩
  have hcomponent : b ∈ connectedComponentIn (A ∪ K)ᶜ a :=
    janiszewski hA hKcompact (hAK ▸ hinter)
      (by simpa only [mem_union, not_or] using And.intro ha.2 haK)
      (by simpa only [mem_union, not_or] using And.intro hb.2 hbK) hcompA hcompK
  obtain ⟨p, hp⟩ :=
    (mem_connectedComponentIn_compl_iff_exists_path_avoiding
      (hA.union hKcompact).isClosed).mp hcomponent
  have hpball : range p ⊆ ball (0 : ℂ) R := by
    apply (isPreconnected_range p.continuous).subset_left_of_subset_union
      isOpen_ball isClosed_closedBall.isOpen_compl
    · exact Set.disjoint_left.mpr (fun _ hz hzc => hzc (ball_subset_closedBall hz))
    · rintro z ⟨t, rfl⟩
      have hz : p t ∉ sphere (0 : ℂ) R := fun hz => hp t (Or.inr (Or.inr hz))
      simp only [mem_ball, mem_compl_iff, mem_closedBall, mem_union]
      rw [mem_sphere] at hz
      exact (lt_or_gt_of_ne hz).imp_right not_le_of_gt
    · exact ⟨a, p.source_mem_range, hR (Or.inr γ.source_mem_range)⟩
  refine ⟨p, ?_⟩
  rintro z ⟨t, rfl⟩
  have ht := hp t
  refine ⟨?_, fun h => ht (Or.inl h)⟩
  by_contra hz
  exact ht (Or.inr (Or.inl ⟨ball_subset_closedBall (hpball ⟨t, rfl⟩), hz⟩))

/-- A compact nonseparating set contained in an open connected plane region can
be avoided within the region. -/
theorem exists_path_avoiding_nonseparating_compact {U A : Set ℂ} (hU : IsOpen U)
    (hconn : IsPreconnected U) (hA : IsCompact A)
    (hsep : ∀ ⦃a b : ℂ⦄, a ∉ A → b ∉ A → ¬ Separates A a b) (hAU : A ⊆ U)
    {a b : ℂ} (ha : a ∈ U \ A) (hb : b ∈ U \ A) :
    ∃ p : Path a b, range p ⊆ U \ A := by
  apply exists_path_avoiding_nonseparating_compact_of_preconnected_inter_compl
    hU hconn hA hsep _ ha hb
  have : A ∩ Uᶜ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hz.2 (hAU hz.1)
  rw [this]
  exact isPreconnected_empty

/-- Points in an open connected plane region can be joined while avoiding a contained arc. -/
theorem exists_path_avoiding_arc {U A : Set ℂ} (hU : IsOpen U)
    (hconn : IsPreconnected U) (hA : IsArcSet A) (hAU : A ⊆ U)
    {a b : ℂ} (ha : a ∈ U \ A) (hb : b ∈ U \ A) :
    ∃ p : Path a b, range p ⊆ U \ A :=
  exists_path_avoiding_nonseparating_compact hU hconn hA.isCompact
    (fun {_ _} ha hb => not_separates_of_isArcSet hA ha hb) hAU ha hb

/-- The range of an injective path is an arc. -/
theorem isArcSet_range {x y : ℂ} (p : Path x y) (hp : Function.Injective p) :
    IsArcSet (range p) := by
  refine ⟨p.extend, p.continuous_extend.continuousOn, ?_, ?_⟩
  · intro s hs t ht hst
    have heq : p ⟨s, hs⟩ = p ⟨t, ht⟩ := by
      simpa only [Path.extend_apply _ hs, Path.extend_apply _ ht] using hst
    exact congrArg Subtype.val (hp heq)
  · exact (p.image_extend_of_subset Subset.rfl).symm

/-- An injective path contained in an open connected region can be avoided. -/
theorem exists_path_avoiding_injective_path {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hconn : IsPreconnected U) {x y a b : ℝ × ℝ} (p : Path x y)
    (hp : Function.Injective p) (hpU : range p ⊆ U)
    (ha : a ∈ U \ range p) (hb : b ∈ U \ range p) :
    ∃ q : Path a b, range q ⊆ U \ range p := by
  let h : (ℝ × ℝ) ≃ₜ ℂ := Complex.equivRealProdCLM.symm.toHomeomorph
  let p' := p.map h.continuous
  have hp' : Function.Injective p' := h.injective.comp hp
  have hrange : range p' = h '' range p := by
    ext z
    simp only [p', Path.map_coe, Function.comp_apply, mem_range, mem_image]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨p t, ⟨t, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
  have himage : ∀ z, z ∈ U \ range p → h z ∈ h '' U \ range p' := by
    intro z hz
    refine ⟨⟨z, hz.1, rfl⟩, ?_⟩
    rw [hrange]
    rintro ⟨w, hw, heq⟩
    exact hz.2 (h.injective heq ▸ hw)
  obtain ⟨q, hq⟩ := exists_path_avoiding_arc (h.isOpenMap _ hU)
    (hconn.image h h.continuous.continuousOn) (isArcSet_range p' hp')
    (by rw [hrange]; exact Set.image_mono hpU) (himage a ha) (himage b hb)
  let q' : Path a b := by
    simpa only [Homeomorph.symm_apply_apply] using q.map h.symm.continuous
  refine ⟨q', ?_⟩
  rintro z ⟨t, rfl⟩
  have ht := hq ⟨t, rfl⟩
  have htU : h.symm (q t) ∈ U := by
    obtain ⟨w, hw, heq⟩ := ht.1
    rw [← heq, Homeomorph.symm_apply_apply]
    exact hw
  have htp : h.symm (q t) ∉ range p := by
    intro hm
    apply ht.2
    rw [hrange]
    exact ⟨h.symm (q t), hm, h.apply_symm_apply _⟩
  exact ⟨htU, htp⟩

/-- Removing a contained injective path from an open preconnected region preserves
preconnectedness. -/
theorem isPreconnected_sdiff_injective_path {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hconn : IsPreconnected U) {x y : ℝ × ℝ} (p : Path x y)
    (hp : Function.Injective p) (hpU : range p ⊆ U) :
    IsPreconnected (U \ range p) := by
  by_cases hne : (U \ range p).Nonempty
  · have hpath : IsPathConnected (U \ range p) := by
      apply isPathConnected_iff.mpr
      refine ⟨hne, ?_⟩
      intro a ha b hb
      obtain ⟨q, hq⟩ := exists_path_avoiding_injective_path hU hconn p hp hpU ha hb
      exact ⟨q, fun t => hq ⟨t, rfl⟩⟩
    exact hpath.isConnected.isPreconnected
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact isPreconnected_empty

/-- Two distinct points in an open region can be joined by a simple polygonal arc
avoiding a given contained injective path. -/
theorem exists_injective_polygonal_path_avoiding_path {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U) {x y a b : ℝ × ℝ}
    (p : Path x y) (hp : Function.Injective p) (hpU : range p ⊆ U)
    (ha : a ∈ U \ range p) (hb : b ∈ U \ range p) (hab : a ≠ b) :
    ∃ q : Path a b, ∃ vs : List (ℝ × ℝ),
      LatticeProb.Topology.IsSimplePolygonalChain vs ∧ Function.Injective q ∧
      range q = LatticeProb.Topology.polygonalChain vs ∧ range q ⊆ U \ range p := by
  obtain ⟨vs, hv, hsub, hhead, hlast⟩ :=
    LatticeProb.Topology.exists_polygonal_chain_of_isPreconnected
      (hU.sdiff (isCompact_range p.continuous).isClosed)
      (isPreconnected_sdiff_injective_path hU hconn p hp hpU) ha hb
  have hvne : vs.head hv ≠ vs.getLast hv := by simpa only [hhead, hlast] using hab
  obtain ⟨us, hu, hs, hh, hl, hsub', hinj, hrange⟩ :=
    LatticeProb.Topology.exists_injective_polygonal_arc vs hv hvne
  let q := (LatticeProb.Topology.polygonalChainPath us hu).cast
    (hh.trans hhead).symm (hl.trans hlast).symm
  exact ⟨q, us, hs, hinj, hrange, hrange ▸ hsub'.trans hsub⟩

/-- Adjoining an arc along a preconnected intersection preserves planar non-separation. -/
theorem not_separates_union_arc {A K : Set ℂ} (hA : IsArcSet A) (hK : IsCompact K)
    (hAK : IsPreconnected (A ∩ K))
    (hKsep : ∀ ⦃a b : ℂ⦄, a ∉ K → b ∉ K → ¬ Separates K a b)
    {a b : ℂ} (ha : a ∉ A ∪ K) (hb : b ∉ A ∪ K) :
    ¬ Separates (A ∪ K) a b := by
  intro h
  exact hKsep (fun hk => ha (Or.inr hk)) (fun hk => hb (Or.inr hk))
    (separates_of_union_with_arc hA hK ha hb hAK h)

end FiniteAvalanches.Electrical.StatementGeometry
