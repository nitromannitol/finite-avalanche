import FiniteAvalanches.Support.Plane.ArcStraightHomeomorph
import FiniteAvalanches.Support.Plane.BoundaryArcJoin

/-!
# Straightening a plane arc from endpoint accesses

Disjoint accesses to the endpoints in the complement of a simple arc give a
closing arc and hence a parameter-preserving homeomorphism of the plane.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

/-- A simple plane arc with disjoint endpoint accesses in its complement admits
parameter-preserving straightening by a homeomorphism of the plane. -/
theorem exists_plane_homeomorph_straightening_of_endpoint_accesses
    {x y a b : ℝ × ℝ} (p : Path x y) (hp : Function.Injective p)
    (q : Path a x) (r : Path b y) (hq : Function.Injective q)
    (hr : Function.Injective r) (hdisj : Disjoint (range q) (range r))
    (hqout : ∀ t : unitInterval, t ≠ 1 → q t ∉ range p)
    (hrout : ∀ t : unitInterval, t ≠ 1 → r t ∉ range p) :
    ∃ F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), ∀ t : unitInterval, F (p t) = (t.val, 0) := by
  let U := (range p)ᶜ
  have hU : IsOpen U := (isCompact_range p.continuous).isClosed.isOpen_compl
  have hconn : IsPreconnected U := by
    simpa only [U, Set.sdiff_eq, Set.univ_inter] using
      (isPreconnected_sdiff_injective_path isOpen_univ isPreconnected_univ p hp
        (subset_univ (range p)))
  have hx : x ∉ U := fun h => h p.source_mem_range
  have hy : y ∉ U := fun h => h p.target_mem_range
  obtain ⟨s, hs, hmeet⟩ := exists_injective_path_between_boundary_accesses hU hconn
    q r hq hr hdisj hqout hrout hx hy
  have hmeet' : range p ∩ range s = {x, y} := by
    simpa only [U, compl_compl, inter_comm] using hmeet
  exact exists_plane_homeomorph_straightening_of_closing_arc p s hp hs hmeet'

private theorem injective_tail {X : Type*} [TopologicalSpace X] {a b : X}
    (q : Path a b) (hq : Function.Injective q) {s : unitInterval} (hs : s ≠ 1) :
    Function.Injective (q.subpath s 1) := by
  intro u v huv
  have h := congrArg Subtype.val (hq huv)
  simp only [Set.Icc.coe_convexComb] at h
  change (1 - (u : ℝ)) * (s : ℝ) + (u : ℝ) * 1 =
    (1 - (v : ℝ)) * (s : ℝ) + (v : ℝ) * 1 at h
  have hs' : (s : ℝ) ≠ 1 := fun h => hs (Subtype.ext h)
  apply Subtype.ext
  have hz : ((u : ℝ) - v) * (1 - (s : ℝ)) = 0 := by nlinarith [h]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hs'.symm))

private theorem exists_tail_in_open {X : Type*} [TopologicalSpace X] {a b : X}
    (q : Path a b) {U : Set X} (hU : IsOpen U) (hb : b ∈ U) :
    ∃ s : unitInterval, s ≠ 1 ∧ range (q.subpath s 1) ⊆ U := by
  have hq : q ⁻¹' U ∈ nhds (1 : unitInterval) := by
    apply q.continuous.continuousAt.tendsto
    simpa only [Path.target] using hU.mem_nhds hb
  obtain ⟨l, hl, hsub⟩ := exists_Ioc_subset_of_mem_nhds hq
    ⟨0, by norm_num⟩
  obtain ⟨s, hls, hs1⟩ := exists_between hl
  refine ⟨s, ne_of_lt hs1, ?_⟩
  rw [Path.range_subpath_of_le q s 1 le_top]
  rintro z ⟨t, ht, rfl⟩
  exact hsub ⟨lt_of_lt_of_le hls ht.1, ht.2⟩

/-- Separate accesses to the endpoints of a simple arc suffice for plane
straightening; the accesses may meet away from the endpoints. -/
theorem exists_plane_homeomorph_straightening_of_separate_endpoint_accesses
    {x y a b : ℝ × ℝ} (p : Path x y) (hp : Function.Injective p)
    (q : Path a x) (r : Path b y) (hq : Function.Injective q)
    (hr : Function.Injective r)
    (hqout : ∀ t : unitInterval, t ≠ 1 → q t ∉ range p)
    (hrout : ∀ t : unitInterval, t ≠ 1 → r t ∉ range p) :
    ∃ F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), ∀ t : unitInterval, F (p t) = (t.val, 0) := by
  have hxy : x ≠ y := by
    intro h
    have heq : (0 : unitInterval) = 1 := hp (by simpa using h)
    norm_num at heq
  obtain ⟨U, V, hU, hV, hx, hy, hUV⟩ := t2_separation hxy
  obtain ⟨s, hs, hsU⟩ := exists_tail_in_open q hU hx
  obtain ⟨t, ht, htV⟩ := exists_tail_in_open r hV hy
  let q' : Path (q s) x := (q.subpath s 1).cast rfl q.target.symm
  let r' : Path (r t) y := (r.subpath t 1).cast rfl r.target.symm
  have hq' : Function.Injective q' := injective_tail q hq hs
  have hr' : Function.Injective r' := injective_tail r hr ht
  have hdisj : Disjoint (range q') (range r') := hUV.mono hsU htV
  have hqout' : ∀ u : unitInterval, u ≠ 1 → q' u ∉ range p := by
    intro u hu hmem
    have hsub : range q' ⊆ range q := by
      change range (q.subpath s 1) ⊆ range q
      rw [Path.range_subpath_of_le q s 1 le_top]
      exact image_subset_range _ _
    obtain ⟨v, hv⟩ := hsub ⟨u, rfl⟩
    have hv1 : v = 1 := by
      by_contra hv1
      exact hqout v hv1 (hv ▸ hmem)
    have hqu : q' u = x := by simpa only [hv1, Path.target] using hv.symm
    apply hu
    apply hq'
    simpa only [Path.target] using hqu
  have hrout' : ∀ u : unitInterval, u ≠ 1 → r' u ∉ range p := by
    intro u hu hmem
    have hsub : range r' ⊆ range r := by
      change range (r.subpath t 1) ⊆ range r
      rw [Path.range_subpath_of_le r t 1 le_top]
      exact image_subset_range _ _
    obtain ⟨v, hv⟩ := hsub ⟨u, rfl⟩
    have hv1 : v = 1 := by
      by_contra hv1
      exact hrout v hv1 (hv ▸ hmem)
    have hru : r' u = y := by simpa only [hv1, Path.target] using hv.symm
    apply hu
    apply hr'
    simpa only [Path.target] using hru
  exact exists_plane_homeomorph_straightening_of_endpoint_accesses p hp q' r'
    hq' hr' hdisj hqout' hrout'


/-- A simple plane arc admits parameter-preserving straightening exactly when
both endpoints can be reached by simple paths from the complement. -/
theorem plane_homeomorph_straightening_iff_endpoint_accesses
    {x y : ℝ × ℝ} (p : Path x y) (hp : Function.Injective p) :
    (∃ F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), ∀ t : unitInterval, F (p t) = (t.val, 0)) ↔
    ∃ (a b : ℝ × ℝ) (q : Path a x) (r : Path b y),
      Function.Injective q ∧ Function.Injective r ∧
      (∀ t : unitInterval, t ≠ 1 → q t ∉ range p) ∧
      (∀ t : unitInterval, t ≠ 1 → r t ∉ range p) := by
  constructor
  · rintro ⟨F, hF⟩
    have hx : F.symm (0, 0) = x := by
      apply F.injective
      simpa using (hF 0).symm
    have hy : F.symm (1, 0) = y := by
      apply F.injective
      simpa using (hF 1).symm
    let q : Path (F.symm (-1, 0)) x :=
      ((Path.segment (-1, 0) (0, 0)).map F.symm.continuous).cast rfl hx.symm
    let r : Path (F.symm (2, 0)) y :=
      ((Path.segment (2, 0) (1, 0)).map F.symm.continuous).cast rfl hy.symm
    have hq : Function.Injective q :=
      F.symm.injective.comp (Path.segment_injective_of_ne (by norm_num))
    have hr : Function.Injective r :=
      F.symm.injective.comp (Path.segment_injective_of_ne (by norm_num))
    refine ⟨_, _, q, r, hq, hr, ?_, ?_⟩
    · intro t ht ⟨u, hu⟩
      have h := congrArg F hu
      rw [hF u] at h
      have hc := congrArg Prod.fst h
      simp only [q, Path.cast_coe, Path.map_coe, Function.comp_apply,
        Homeomorph.apply_symm_apply, Path.segment_apply, AffineMap.lineMap_apply_module,
        Prod.fst_add] at hc
      change (u : ℝ) = (1 - (t : ℝ)) * (-1) + (t : ℝ) * 0 at hc
      have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2
        (fun heq => ht (Subtype.ext heq))
      linarith [u.property.1]
    · intro t ht ⟨u, hu⟩
      have h := congrArg F hu
      rw [hF u] at h
      have hc := congrArg Prod.fst h
      simp only [r, Path.cast_coe, Path.map_coe, Function.comp_apply,
        Homeomorph.apply_symm_apply, Path.segment_apply, AffineMap.lineMap_apply_module,
        Prod.fst_add] at hc
      change (u : ℝ) = (1 - (t : ℝ)) * 2 + (t : ℝ) * 1 at hc
      have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2
        (fun heq => ht (Subtype.ext heq))
      linarith [u.property.2]
  · rintro ⟨a, b, q, r, hq, hr, hqout, hrout⟩
    exact exists_plane_homeomorph_straightening_of_separate_endpoint_accesses
      p hp q r hq hr hqout hrout

/-- An access to an initial subarc can be shortened to avoid the whole arc. -/
theorem exists_endpoint_access_of_initial_subpath
    {x y a : ℝ × ℝ} (p : Path x y) (hp : Function.Injective p)
    (s : unitInterval) (hs : s ≠ 0) (q : Path a x) (hq : Function.Injective q)
    (hout : ∀ t : unitInterval, t ≠ 1 → q t ∉ range (p.subpath 0 s)) :
    ∃ b : ℝ × ℝ, ∃ r : Path b x, Function.Injective r ∧
      ∀ t : unitInterval, t ≠ 1 → r t ∉ range p := by
  have hx : x ∉ range (p.subpath s 1) := by
    rw [Path.range_subpath_of_le p s 1 le_top]
    rintro ⟨t, ht, heq⟩
    have ht0 : t = 0 := hp (by simpa only [Path.source] using heq)
    have : s ≤ 0 := ht0 ▸ ht.1
    exact hs (le_antisymm this bot_le)
  let U := (range (p.subpath s 1))ᶜ
  have hU : IsOpen U := (isCompact_range (p.subpath s 1).continuous).isClosed.isOpen_compl
  obtain ⟨u, hu, huU⟩ := exists_tail_in_open q hU hx
  let r : Path (q u) x := (q.subpath u 1).cast rfl q.target.symm
  refine ⟨q u, r, injective_tail q hq hu, ?_⟩
  intro t ht hmem
  have hnot : r t ∉ range (p.subpath s 1) := huU ⟨t, rfl⟩
  obtain ⟨v, hv⟩ := hmem
  by_cases hvle : v ≤ s
  · have hvsub : p v ∈ range (p.subpath 0 s) := by
      rw [Path.range_subpath_of_le p 0 s bot_le]
      exact ⟨v, ⟨bot_le, hvle⟩, rfl⟩
    have hrt : r t ∉ range (p.subpath 0 s) := by
      have hsub : range r ⊆ range q := by
        change range (q.subpath u 1) ⊆ range q
        rw [Path.range_subpath_of_le q u 1 le_top]
        exact image_subset_range _ _
      obtain ⟨w, hw⟩ := hsub ⟨t, rfl⟩
      change q w = (q.subpath u 1) t at hw
      have hw1 : w ≠ 1 := by
        intro hw1
        apply ht
        apply injective_tail q hq hu
        simpa only [hw1, Path.target] using hw.symm
      exact hw ▸ hout w hw1
    exact hrt (hv ▸ hvsub)
  · apply hnot
    rw [Path.range_subpath_of_le p s 1 le_top]
    exact ⟨v, ⟨le_of_not_ge hvle, le_top⟩, hv⟩


/-- Local accesses to the two endpoint subarcs suffice for parameter-preserving
plane straightening of the entire arc. -/
theorem exists_plane_homeomorph_straightening_of_local_endpoint_accesses
    {x y a b : ℝ × ℝ} (p : Path x y) (hp : Function.Injective p)
    (s t : unitInterval) (hs : s ≠ 0) (ht : t ≠ 0)
    (q : Path a x) (r : Path b y) (hq : Function.Injective q)
    (hr : Function.Injective r)
    (hqout : ∀ u : unitInterval, u ≠ 1 → q u ∉ range (p.subpath 0 s))
    (hrout : ∀ u : unitInterval, u ≠ 1 → r u ∉ range (p.symm.subpath 0 t)) :
    ∃ F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), ∀ u : unitInterval, F (p u) = (u.val, 0) := by
  obtain ⟨a', q', hq', hqout'⟩ :=
    exists_endpoint_access_of_initial_subpath p hp s hs q hq hqout
  have hp' : Function.Injective p.symm := hp.comp unitInterval.symm_involutive.injective
  obtain ⟨b', r', hr', hrout'⟩ :=
    exists_endpoint_access_of_initial_subpath p.symm hp' t ht r hr hrout
  have hrout'' : ∀ u : unitInterval, u ≠ 1 → r' u ∉ range p := by
    simpa only [Path.symm_range] using hrout'
  exact exists_plane_homeomorph_straightening_of_separate_endpoint_accesses
    p hp q' r' hq' hr' hqout' hrout''

end FiniteAvalanches.Electrical.StatementGeometry
