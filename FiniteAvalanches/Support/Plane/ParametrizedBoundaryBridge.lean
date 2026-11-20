import FiniteAvalanches.Support.Plane.ParametrizedBoundaryTwoStar

/-!
# Parametrized boundary arms with a common endpoint

Two boundary accesses that meet only at their common endpoint admit separated
rooted arms retaining both terminal parametrizations.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

private theorem subpath_inj {a b : ℝ × ℝ} (p : Path a b) (hp : Function.Injective p)
    {s t : unitInterval} (hst : s ≠ t) : Function.Injective (p.subpath s t) := by
  intro u v huv
  have h := congrArg Subtype.val (hp huv)
  simp only [Set.Icc.coe_convexComb] at h
  have hst' : (s : ℝ) ≠ t := fun h => hst (Subtype.ext h)
  apply Subtype.ext
  have hz : ((u : ℝ) - v) * ((t : ℝ) - s) = 0 := by nlinarith [h]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr (Ne.symm hst')))

/-- Two boundary accesses meeting only at their common endpoint admit arms
that meet only at their root and common endpoint, with exact terminal speed. -/
theorem exists_two_boundary_arms_common_endpoint
    {U S : Set (ℝ × ℝ)} {a c b : ℝ × ℝ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (p : Path a b) (q : Path c b) (hp : Function.Injective p)
    (hq : Function.Injective q) (hd : Disjoint (range p ∩ U) (range q))
    (hpU : ∀ t : unitInterval, t ≠ 1 → p t ∈ U)
    (hqU : ∀ t : unitInterval, t ≠ 1 → q t ∈ U)
    (hb : b ∉ U) (hS : S.Finite)
    (hpS : Disjoint (range p) S) (hqS : Disjoint (range q) S) :
    ∃ r ∈ U, ∃ (v w : Path r b),
      Function.Injective v ∧ Function.Injective w ∧
      Disjoint (range v) S ∧ Disjoint (range w) S ∧
      range v ∩ range w = {r, b} ∧
      range v ∩ Uᶜ = {b} ∧ range w ∩ Uᶜ = {b} ∧
      (∃ u : unitInterval, u ≠ 1 ∧
        ∀ (t : unitInterval) (ht : ((u : ℝ) + 1) / 2 ≤ (t : ℝ)),
          v t = p ⟨2 * (t : ℝ) - 1, by
            constructor
            · have := u.property.1
              linarith
            · linarith [t.property.2]⟩) ∧
      (∃ u : unitInterval, u ≠ 1 ∧
        ∀ (t : unitInterval) (ht : ((u : ℝ) + 1) / 2 ≤ (t : ℝ)),
          w t = q ⟨2 * (t : ℝ) - 1, by
            constructor
            · have := u.property.1
              linarith
            · linarith [t.property.2]⟩) := by
  let m : unitInterval := ⟨1 / 2, by norm_num⟩
  have hm0 : m ≠ 0 := by
    intro h
    have h' := congrArg Subtype.val h
    norm_num [m] at h'
  have hm1 : m ≠ 1 := by
    intro h
    have h' := congrArg Subtype.val h
    norm_num [m] at h'
  let head : Path a (p m) := (p.subpath 0 m).cast p.source.symm rfl
  let tail : Path (p m) b := (p.subpath m 1).cast rfl p.target.symm
  have hhead : Function.Injective head := subpath_inj p hp hm0.symm
  have htail : Function.Injective tail := subpath_inj p hp hm1
  have hheadsub : range head ⊆ range p := by
    change range (p.subpath 0 m) ⊆ _
    rw [Path.range_subpath]
    exact image_subset_range _ _
  have htailsub : range tail ⊆ range p := by
    change range (p.subpath m 1) ⊆ _
    rw [Path.range_subpath]
    exact image_subset_range _ _
  have htailU : ∀ t : unitInterval, t ≠ 1 → tail t ∈ U := by
    intro t ht
    apply hpU
    intro heq
    have h := congrArg Subtype.val heq
    simp only [Set.Icc.coe_convexComb] at h
    norm_num [m] at h
    change (1 - (t : ℝ)) * (1 / 2) + (t : ℝ) = 1 at h
    apply ht
    apply Subtype.ext
    change (t : ℝ) = 1
    linarith
  let W : Set (ℝ × ℝ) := U \ range tail
  have hW : IsOpen W := hU.sdiff (isCompact_range tail.continuous).isClosed
  have hWconn : IsPreconnected W := by
    let paths : Unit → Path (p m) b := fun _ => tail
    have h := isPreconnected_sdiff_finset_paths_of_disjoint_inside hU hconn
      ({()} : Finset Unit) paths (by simpa [paths] using htail) (by simp)
      (by simpa [paths] using
        isPreconnected_range_inter_compl_of_mem_except_target tail htailU hb)
    simpa [W, paths, iUnion_const] using h
  have hheadW : ∀ t : unitInterval, t ≠ 1 → head t ∈ W := by
    intro t ht
    have htlt : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 (fun h => ht (Subtype.ext h))
    have hpar : (Set.Icc.convexComb (0 : unitInterval) m t : ℝ) < m := by
      simp only [Set.Icc.coe_convexComb]
      change (1 - (t : ℝ)) * 0 + (t : ℝ) * (1 / 2) < (1 / 2 : ℝ)
      linarith
    refine ⟨hpU _ ?_, ?_⟩
    · intro heq
      have h := congrArg Subtype.val heq
      change (Set.Icc.convexComb (0 : unitInterval) m t : ℝ) = 1 at h
      have hlt : (Set.Icc.convexComb (0 : unitInterval) m t : ℝ) < 1 :=
        hpar.trans (by norm_num [m])
      exact (ne_of_lt hlt) h
    · intro hmem
      change p (Set.Icc.convexComb 0 m t) ∈ range (p.subpath m 1) at hmem
      rw [Path.range_subpath_of_le p m 1 le_top] at hmem
      obtain ⟨u, hu, heq⟩ := hmem
      have heq' := congrArg Subtype.val (hp heq)
      have := hu.1
      change (m : ℝ) ≤ u at this
      linarith
  have hqW : ∀ t : unitInterval, t ≠ 1 → q t ∈ W := by
    intro t ht
    have htU := hqU t ht
    refine ⟨htU, ?_⟩
    intro hmem
    exact disjoint_left.mp hd ⟨htailsub hmem, htU⟩ ⟨t, rfl⟩
  have hheadq : Disjoint (range head) (range q) := by
    apply disjoint_left.mpr
    intro z hz hqz
    apply disjoint_left.mp hd ⟨hheadsub hz, ?_⟩ hqz
    obtain ⟨t, rfl⟩ := hz
    apply hpU
    intro heq
    have hh := congrArg Subtype.val heq
    simp only [Set.Icc.coe_convexComb] at hh
    norm_num [m] at hh
    linarith [t.property.2]
  have hmW : p m ∉ W := fun h => h.2 tail.source_mem_range
  have hbW : b ∉ W := fun h => hb h.1
  obtain ⟨r, hr, v, w, hv, hw, hvS, hwS, hvw, hvW, hwW,
    _, ⟨z, hz, hzspeed⟩⟩ :=
    exists_two_boundary_arms_with_parametrized_tails hW hWconn head q hhead hq hheadq
      hheadW hqW hmW hbW hS (hpS.mono_left hheadsub) hqS
  have hvTail : range v ∩ range tail = {p m} := by
    apply subset_antisymm
    · rintro x ⟨hxv, hxt⟩
      have hxW : x ∈ Wᶜ := fun hx => hx.2 hxt
      exact hvW ▸ ⟨hxv, hxW⟩
    · exact singleton_subset_iff.mpr ⟨v.target_mem_range, tail.source_mem_range⟩
  have hinj : Function.Injective (v.trans tail) :=
    LatticeProb.Topology.path_trans_injective hv htail hvTail
  obtain ⟨v', hv', hv'range, hspeed⟩ :=
    path_trans_subpath_reparam_terminal p m hm1 v hinj
  let v'' : Path r b := v'.cast rfl p.target.symm
  have hrange : range v'' = range v ∪ range tail := by
    change range v' = _
    rw [hv'range, Path.trans_range]
    rfl
  refine ⟨r, hr.1, v'', w, hv', hw, ?_, hwS, ?_, ?_, ?_, ⟨m, hm1, hspeed⟩,
    ⟨z, hz, hzspeed⟩⟩
  · rw [hrange]
    exact disjoint_union_left.mpr ⟨hvS, hpS.mono_left htailsub⟩
  · apply subset_antisymm
    · intro x hx
      rw [hrange] at hx
      rcases hx.1 with hxv | hxt
      · have h : x = r := mem_singleton_iff.mp (hvw ▸ ⟨hxv, hx.2⟩)
        simp [h]
      · by_cases hxU : x ∈ W
        · exact (hxU.2 hxt).elim
        · have h : x = b := mem_singleton_iff.mp (hwW ▸ ⟨hx.2, hxU⟩)
          simp [h]
    · intro x hx
      simp only [mem_insert_iff, mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨v''.source_mem_range, w.source_mem_range⟩
      · exact ⟨v''.target_mem_range, w.target_mem_range⟩
  · apply subset_antisymm
    · rintro x ⟨hx, hxU⟩
      rw [hrange] at hx
      rcases hx with hx | hx
      · have h : x = p m := mem_singleton_iff.mp (hvW ▸ ⟨hx, fun hh => hxU hh.1⟩)
        exact (hxU (h ▸ hpU m hm1)).elim
      · rw [← range_inter_compl_of_mem_except_target tail htailU hb]
        exact ⟨hx, hxU⟩
    · exact singleton_subset_iff.mpr ⟨v''.target_mem_range, hb⟩
  · apply subset_antisymm
    · rintro x ⟨hx, hxU⟩
      exact hwW ▸ ⟨hx, fun hh => hxU hh.1⟩
    · exact singleton_subset_iff.mpr ⟨w.target_mem_range, hb⟩

end FiniteAvalanches.Electrical.StatementGeometry
