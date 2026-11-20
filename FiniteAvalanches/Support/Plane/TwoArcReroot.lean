import FiniteAvalanches.Support.Plane.BoundaryTripodTails

/-!
# Rerooting two arcs

Two arcs with common endpoints can be split and rerooted at an interior point
of either arc, without changing their union.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

private theorem subpath_injective_of_ne {X : Type*} [TopologicalSpace X]
    {a b : X} (p : Path a b) (hp : Function.Injective p)
    {s t : unitInterval} (hst : s ≠ t) : Function.Injective (p.subpath s t) := by
  intro u v huv
  have h := congrArg Subtype.val (hp huv)
  simp only [Set.Icc.coe_convexComb] at h
  have hst' : (s : ℝ) ≠ t := fun h => hst (Subtype.ext h)
  apply Subtype.ext
  have hz : ((u : ℝ) - v) * ((t : ℝ) - s) = 0 := by nlinarith [h]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hst'.symm))

/-- Reroot two arcs at a point of the first arc, preserving a terminal subarc
of the first and the entire second arc in different branches. -/
theorem exists_reroot_two_arcs_of_mem_left {X : Type*} [TopologicalSpace X]
    {a b r : X} (p q : Path a b) (hp : Function.Injective p) (hq : Function.Injective q)
    (hpq : range p ∩ range q = {a, b}) (hr : r ∈ range p) (hrb : r ≠ b) :
    ∃ (v w : Path r b), Function.Injective v ∧ Function.Injective w ∧
      range v ∩ range w = {r, b} ∧
      range v ∪ range w = range p ∪ range q ∧
      (∃ t : unitInterval, t ≠ 1 ∧ range (p.subpath t 1) ⊆ range v) ∧
      range q ⊆ range w := by
  obtain ⟨t, rfl⟩ := hr
  have ht1 : t ≠ 1 := fun h => hrb (by simp only [h, Path.target])
  by_cases ht0 : t = 0
  · subst t
    let v : Path (p 0) b := p.cast p.source rfl
    let w : Path (p 0) b := q.cast p.source rfl
    have hsub : range (p.subpath 0 1) ⊆ range v := by
      rw [Path.range_subpath_of_le p 0 1 bot_le]
      exact image_subset_range _ _
    exact ⟨v, w, hp, hq, by
      change range p ∩ range q = {p 0, b}
      simpa only [Path.source] using hpq, rfl,
      ⟨0, by norm_num, hsub⟩, subset_rfl⟩
  let p0 : Path (p t) a := ((p.subpath 0 t).symm).cast rfl p.source.symm
  let p1 : Path (p t) b := (p.subpath t 1).cast rfl p.target.symm
  have hp0 : Function.Injective p0 :=
    (subpath_injective_of_ne p hp (Ne.symm ht0)).comp unitInterval.symm_involutive.injective
  have hp1 : Function.Injective p1 := subpath_injective_of_ne p hp ht1
  have hp0range : range p0 = p '' Icc 0 t := by
    change range (p.subpath 0 t).symm = _
    rw [Path.symm_range, Path.range_subpath_of_le p 0 t bot_le]
  have hp1range : range p1 = p '' Icc t 1 := Path.range_subpath_of_le p t 1 le_top
  have hp0sub : range p0 ⊆ range p := by rw [hp0range]; exact image_subset_range _ _
  have hp1sub : range p1 ⊆ range p := by rw [hp1range]; exact image_subset_range _ _
  have hp0b : b ∉ range p0 := by
    intro h
    obtain ⟨s, hs, he⟩ := hp0range ▸ h
    have hs1 : s = 1 := hp (he.trans p.target.symm)
    have h1t : (1 : unitInterval) ≤ t := by simpa only [hs1] using hs.2
    exact ht1 (le_antisymm le_top h1t)
  have hp1a : a ∉ range p1 := by
    intro h
    obtain ⟨s, hs, he⟩ := hp1range ▸ h
    have hs0 : s = 0 := hp (he.trans p.source.symm)
    have ht0' : t ≤ (0 : unitInterval) := by simpa only [hs0] using hs.1
    exact ht0 (le_antisymm ht0' bot_le)
  have hjoin : range p0 ∩ range q = {a} := by
    apply subset_antisymm
    · intro z hz
      have h : z ∈ ({a, b} : Set X) := hpq ▸ ⟨hp0sub hz.1, hz.2⟩
      rcases h with h | h
      · exact h
      · exact (hp0b (h ▸ hz.1)).elim
    · exact singleton_subset_iff.mpr ⟨p0.target_mem_range, q.source_mem_range⟩
  have hpart : range p1 ∩ range p0 = {p t} := by
    rw [hp1range, hp0range, ← image_inter hp]
    have heq : Icc t (1 : unitInterval) ∩ Icc 0 t = {t} := by
      ext z
      simp only [mem_inter_iff, mem_Icc, mem_singleton_iff]
      constructor
      · rintro ⟨⟨h1, _⟩, ⟨_, h2⟩⟩
        exact le_antisymm h2 h1
      · rintro rfl
        exact ⟨⟨le_rfl, le_top⟩, ⟨bot_le, le_rfl⟩⟩
    rw [heq, image_singleton]
  have hpartq : range p1 ∩ range q = {b} := by
    apply subset_antisymm
    · intro z hz
      have h : z ∈ ({a, b} : Set X) := hpq ▸ ⟨hp1sub hz.1, hz.2⟩
      rcases h with h | h
      · exact (hp1a (h ▸ hz.1)).elim
      · exact h
    · exact singleton_subset_iff.mpr ⟨p1.target_mem_range, q.target_mem_range⟩
  have hcover : range p0 ∪ range p1 = range p := by
    apply subset_antisymm (union_subset hp0sub hp1sub)
    rintro z ⟨s, rfl⟩
    rcases le_total s t with h | h
    · exact Or.inl (hp0range.symm ▸ ⟨s, ⟨bot_le, h⟩, rfl⟩)
    · exact Or.inr (hp1range.symm ▸ ⟨s, ⟨h, le_top⟩, rfl⟩)
  let v := p1
  let w := p0.trans q
  refine ⟨v, w, hp1, LatticeProb.Topology.path_trans_injective hp0 hq hjoin, ?_, ?_,
    ⟨t, ht1, subset_rfl⟩, ?_⟩
  · rw [show range w = range p0 ∪ range q from Path.trans_range p0 q,
      inter_union_distrib_left, hpart, hpartq]
    ext z
    simp only [mem_union, mem_singleton_iff, mem_insert_iff]
  · rw [show range w = range p0 ∪ range q from Path.trans_range p0 q]
    rw [← union_assoc, union_comm (range p1) (range p0), hcover]
  · rw [show range w = range p0 ∪ range q from Path.trans_range p0 q]
    exact subset_union_right

end FiniteAvalanches.Electrical.StatementGeometry
