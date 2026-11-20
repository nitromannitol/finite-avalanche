import FiniteAvalanches.Support.Plane.BoundaryTwoStar

/-!
# Attaching a third arm to an arc

The first meeting of a path with a simple arc splits the arc into two arms.
The initial segment of the path supplies a third arm.
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

/-- A simple arc and a simple path meeting its interior contain three simple
arms with a common root and otherwise disjoint images. -/
theorem exists_tripod_of_path_first_hit {X : Type*} [TopologicalSpace X] [T2Space X]
    {a b c d : X} (p : Path a b) (q : Path c d)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hc : c ∉ range p) (hd : d ∈ range p)
    (ha : a ∉ range q) (hb : b ∉ range q) :
    ∃ (r : X) (u : Path r a) (v : Path r b) (w : Path r c),
      Function.Injective u ∧ Function.Injective v ∧ Function.Injective w ∧
      range u ⊆ range p ∧ range v ⊆ range p ∧ range w ⊆ range q ∧
      range u ∩ range v = {r} ∧ range u ∩ range w = {r} ∧
      range v ∩ range w = {r} ∧ range p = range u ∪ range v := by
  obtain ⟨r, hr, z, hz, hzsub, hzmeet⟩ :=
    exists_initial_path_first_hit q hq (isCompact_range p.continuous).isClosed hc hd
  obtain ⟨t, rfl⟩ := hr
  have ht0 : t ≠ 0 := by
    intro ht
    apply ha
    have h : p t ∈ range q := hzsub z.target_mem_range
    simpa only [ht, Path.source] using h
  have ht1 : t ≠ 1 := by
    intro ht
    apply hb
    have h : p t ∈ range q := hzsub z.target_mem_range
    simpa only [ht, Path.target] using h
  let u : Path (p t) a := ((p.subpath 0 t).symm).cast rfl p.source.symm
  let v : Path (p t) b := (p.subpath t 1).cast rfl p.target.symm
  let w : Path (p t) c := z.symm
  have hu : Function.Injective u :=
    (subpath_injective_of_ne p hp ht0.symm).comp unitInterval.symm_involutive.injective
  have hv : Function.Injective v := subpath_injective_of_ne p hp ht1
  have hw : Function.Injective w := hz.comp unitInterval.symm_involutive.injective
  have hurange : range u = p '' Icc 0 t := by
    change range (p.subpath 0 t).symm = _
    rw [Path.symm_range, Path.range_subpath_of_le p 0 t bot_le]
  have hvrange : range v = p '' Icc t 1 := Path.range_subpath_of_le p t 1 le_top
  have husub : range u ⊆ range p := by rw [hurange]; exact image_subset_range _ _
  have hvsub : range v ⊆ range p := by rw [hvrange]; exact image_subset_range _ _
  have hwsub : range w ⊆ range q := by simpa only [w, Path.symm_range] using hzsub
  have huv : range u ∩ range v = {p t} := by
    rw [hurange, hvrange, ← image_inter hp]
    have heq : Icc (0 : unitInterval) t ∩ Icc t 1 = {t} := by
      ext x
      simp only [mem_inter_iff, mem_Icc, mem_singleton_iff]
      constructor
      · rintro ⟨⟨_, hx⟩, ⟨hy, _⟩⟩
        exact le_antisymm hx hy
      · rintro rfl
        exact ⟨⟨bot_le, le_rfl⟩, ⟨le_rfl, le_top⟩⟩
    rw [heq, image_singleton]
  have hwmeet : range w ∩ range p = {p t} := by
    simpa only [w, Path.symm_range] using hzmeet
  have huw : range u ∩ range w = {p t} := by
    apply subset_antisymm
    · intro x hx
      rw [← hwmeet]
      exact ⟨hx.2, husub hx.1⟩
    · exact singleton_subset_iff.mpr ⟨u.source_mem_range, w.source_mem_range⟩
  have hvw : range v ∩ range w = {p t} := by
    apply subset_antisymm
    · intro x hx
      rw [← hwmeet]
      exact ⟨hx.2, hvsub hx.1⟩
    · exact singleton_subset_iff.mpr ⟨v.source_mem_range, w.source_mem_range⟩
  refine ⟨p t, u, v, w, hu, hv, hw, husub, hvsub, hwsub, huv, huw, hvw, ?_⟩
  apply subset_antisymm
  · rintro x ⟨s, rfl⟩
    rcases le_total s t with h | h
    · exact Or.inl (hurange.symm ▸ ⟨s, ⟨bot_le, h⟩, rfl⟩)
    · exact Or.inr (hvrange.symm ▸ ⟨s, ⟨h, le_top⟩, rfl⟩)
  · exact union_subset husub hvsub

end FiniteAvalanches.Electrical.StatementGeometry
