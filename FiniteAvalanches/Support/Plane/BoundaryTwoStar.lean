import FiniteAvalanches.Support.Plane.BoundaryArcJoinTails

/-!
# Two boundary arms

Two distinct boundary accesses admit separated arms from one interior point,
retaining terminal subarcs of both accesses.
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

/-- Two disjoint boundary accesses admit separated rooted arms preserving
terminal subpaths and avoiding a finite set. -/
theorem exists_two_boundary_arms_with_tails
    {U S : Set (ℝ × ℝ)} {a b c d : ℝ × ℝ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (p : Path a b) (q : Path c d) (hp : Function.Injective p)
    (hq : Function.Injective q) (hd : Disjoint (range p) (range q))
    (hpU : ∀ t : unitInterval, t ≠ 1 → p t ∈ U)
    (hqU : ∀ t : unitInterval, t ≠ 1 → q t ∈ U)
    (hb : b ∉ U) (hd' : d ∉ U)
    (hS : S.Finite) (hpS : Disjoint (range p) S) (hqS : Disjoint (range q) S) :
    ∃ r ∈ U, ∃ (v : Path r b) (w : Path r d),
      Function.Injective v ∧ Function.Injective w ∧
      Disjoint (range v) S ∧ Disjoint (range w) S ∧
      range v ∩ range w = {r} ∧
      range v ∩ Uᶜ = {b} ∧ range w ∩ Uᶜ = {d} ∧
      (∃ t : unitInterval, t ≠ 1 ∧ range (p.subpath t 1) ⊆ range v) ∧
      (∃ t : unitInterval, t ≠ 1 ∧ range (q.subpath t 1) ⊆ range w) := by
  obtain ⟨a, ha, haS, habound, ⟨tp, htp, hp_tail⟩, ⟨tq, htq, hq_tail⟩⟩ :=
    exists_injective_path_between_boundary_accesses_with_tails
      hU hconn p q hp hq hd hpU hqU hb hd' hS hpS hqS
  let m : unitInterval := ⟨1 / 2, by norm_num⟩
  let r := a m
  let v : Path r b := (a.subpath m 1).cast rfl a.target.symm
  let w : Path r d := ((a.subpath 0 m).symm).cast rfl a.source.symm
  have hm0 : m ≠ 0 := by
    intro h
    have hh := congrArg Subtype.val h
    norm_num [m] at hh
  have hm1 : m ≠ 1 := by
    intro h
    have hh := congrArg Subtype.val h
    norm_num [m] at hh
  have hv : Function.Injective v := subpath_inj a ha hm1
  have hw' : Function.Injective (a.subpath 0 m) := subpath_inj a ha hm0.symm
  have hw : Function.Injective w := by
    intro x y h
    exact unitInterval.symm_involutive.injective (hw' h)
  have hvrange : range v = a '' Icc m 1 := Path.range_subpath_of_le a m 1 le_top
  have hwrange : range w = a '' Icc 0 m := by
    change range (a.subpath 0 m).symm = _
    rw [Path.symm_range, Path.range_subpath_of_le a 0 m bot_le]
  have hrange : range v ∩ range w = {r} := by
    rw [hvrange, hwrange, ← Set.image_inter ha]
    have heq : Icc m (1 : unitInterval) ∩ Icc 0 m = {m} := by
      ext x
      simp only [mem_inter_iff, mem_Icc, mem_singleton_iff]
      constructor
      · rintro ⟨⟨h1, _⟩, ⟨_, h2⟩⟩
        exact le_antisymm h2 h1
      · rintro rfl
        exact ⟨⟨le_rfl, le_top⟩, ⟨bot_le, le_rfl⟩⟩
    rw [heq, image_singleton]
  have hsubv : range v ⊆ range a := by rw [hvrange]; exact image_subset_range _ _
  have hsubw : range w ⊆ range a := by rw [hwrange]; exact image_subset_range _ _
  have hrU : r ∈ U := by
    by_contra hr
    have h : r ∈ ({d, b} : Set (ℝ × ℝ)) := habound ▸ ⟨⟨m, rfl⟩, hr⟩
    simp only [mem_insert_iff, mem_singleton_iff] at h
    rcases h with h | h
    · exact hm0 (ha (h.trans a.source.symm))
    · exact hm1 (ha (h.trans a.target.symm))
  have hvbound : range v ∩ Uᶜ = {b} := by
    apply subset_antisymm
    · intro x hx
      have h : x ∈ ({d, b} : Set (ℝ × ℝ)) := habound ▸ ⟨hsubv hx.1, hx.2⟩
      simp only [mem_insert_iff, mem_singleton_iff] at h
      rcases h with h | h
      · subst x
        obtain ⟨t, ht, heq⟩ := hvrange ▸ hx.1
        have ht0 : t = 0 := ha (heq.trans a.source.symm)
        have : m ≤ 0 := by simpa only [ht0] using ht.1
        exact (hm0 (le_antisymm this bot_le)).elim
      · exact mem_singleton_iff.mpr h
    · exact singleton_subset_iff.mpr ⟨v.target_mem_range, hb⟩
  have hwbound : range w ∩ Uᶜ = {d} := by
    apply subset_antisymm
    · intro x hx
      have h : x ∈ ({d, b} : Set (ℝ × ℝ)) := habound ▸ ⟨hsubw hx.1, hx.2⟩
      simp only [mem_insert_iff, mem_singleton_iff] at h
      rcases h with h | h
      · exact mem_singleton_iff.mpr h
      · subst x
        obtain ⟨t, ht, heq⟩ := hwrange ▸ hx.1
        have ht1 : t = 1 := ha (heq.trans a.target.symm)
        have : (1 : unitInterval) ≤ m := by simpa only [ht1] using ht.2
        exact (hm1 (le_antisymm le_top this)).elim
    · exact singleton_subset_iff.mpr ⟨w.target_mem_range, hd'⟩
  have harev : Function.Injective a.symm := by
    intro x y h
    exact unitInterval.symm_involutive.injective (ha h)
  obtain ⟨u, hu, husub⟩ := terminal_subpath_in_initial_reverse a p ha htp hm0 hp_tail
  obtain ⟨z, hz, hzsub⟩ := terminal_subpath_in_initial_reverse a.symm q harev htq hm0 (by
    simpa only [Path.symm_range] using hq_tail)
  have hvrev : range (a.symm.subpath 0 m) = range v := by
    rw [Path.range_subpath_of_le a.symm 0 m bot_le, hvrange]
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨unitInterval.symm t, ?_, rfl⟩
      constructor
      · change (m : ℝ) ≤ 1 - (t : ℝ)
        have ht' : (t : ℝ) ≤ m := ht.2
        dsimp [m] at *
        linarith
      · exact le_top
    · rintro ⟨t, ht, rfl⟩
      refine ⟨unitInterval.symm t, ?_, ?_⟩
      · constructor
        · exact bot_le
        · change 1 - (t : ℝ) ≤ m
          have ht' : (m : ℝ) ≤ t := ht.1
          dsimp [m] at *
          linarith
      · change a (unitInterval.symm (unitInterval.symm t)) = a t
        rw [unitInterval.symm_symm]
  refine ⟨r, hrU, v, w, hv, hw, haS.mono_left hsubv, haS.mono_left hsubw,
    hrange, hvbound, hwbound, ⟨u, hu, ?_⟩, ⟨z, hz, ?_⟩⟩
  · simpa only [hvrev] using husub
  · rw [Path.symm_symm] at hzsub
    rw [hwrange, ← Path.range_subpath_of_le a 0 m bot_le]
    exact hzsub

end FiniteAvalanches.Electrical.StatementGeometry
