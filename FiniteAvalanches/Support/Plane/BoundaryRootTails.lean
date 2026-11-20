import FiniteAvalanches.Support.Plane.BoundaryStarExtension
import FiniteAvalanches.Support.Plane.RetainedTailReparam

/-!
# Boundary access to a rooted tree with a retained tail

An accessible boundary point can be joined to a rooted arc tree while
preserving the terminal parametrization of the boundary access.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- A boundary access avoiding a rooted tree and a free root stub extends to
an injective path meeting the tree only at its root, with its terminal speed
preserved. -/
theorem exists_boundary_path_to_root_of_stub_with_tail
    {U K S : Set (ℝ × ℝ)} {r q x b : ℝ × ℝ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hK : IsFiniteArcTree r K)
    (hKU : K ⊆ U) (hS : S.Finite) (p : Path q r) (hp : Function.Injective p)
    (hpU : range p ⊆ U \ S) (hpK : range p ∩ K = {r}) (hq : q ∉ K)
    (a : Path x b) (ha : Function.Injective a)
    (haU : ∀ t : unitInterval, t ≠ 1 → a t ∈ U) (hb : b ∉ U)
    (haS : Disjoint (range a) S) (haK : Disjoint (range a) (K ∪ range p)) :
    ∃ w : Path r b, Function.Injective w ∧ range w ⊆ (U ∪ {b}) \ S ∧
      range w ∩ K = {r} ∧
      ∃ u : unitInterval, u ≠ 1 ∧
        ∀ (t : unitInterval) (ht : ((u : ℝ) + 1) / 2 ≤ (t : ℝ)),
          w t = a ⟨2 * (t : ℝ) - 1, by
            constructor
            · have := u.property.1
              linarith
            · linarith [t.property.2]⟩ := by
  have hxU : x ∈ U := by simpa only [Path.source] using haU 0 (by norm_num)
  have hxK : x ∉ K := fun h => disjoint_left.mp haK a.source_mem_range (Or.inl h)
  have hxp : x ∉ range p := fun h => disjoint_left.mp haK a.source_mem_range (Or.inr h)
  have hxS : x ∉ S := fun h => disjoint_left.mp haS a.source_mem_range h
  obtain ⟨v, hv, hvU, hvK⟩ := exists_path_to_root_of_stub hU hconn hK hKU hS p hp hpU hpK
    ⟨⟨⟨hxU, hxK⟩, hxS⟩, hxp⟩ hq
  have hrK : r ∈ K := by
    have h : r ∈ range p ∩ K := by rw [hpK]; exact mem_singleton r
    exact h.2
  have hra : r ∉ range a := fun h => disjoint_left.mp haK h (Or.inl hrK)
  have hvrev : Function.Injective v.symm := by
    intro s t h
    exact unitInterval.symm_involutive.injective (hv h)
  obtain ⟨z, hz, w, hw, hwsub, hwmeet⟩ :=
    exists_initial_path_first_hit v.symm hvrev (isCompact_range a.continuous).isClosed
      hra a.source_mem_range
  obtain ⟨u, hu⟩ := hz
  have hzU : z ∈ U := (hvU (by simpa only [Path.symm_range] using hwsub w.target_mem_range)).1
  have hu1 : u ≠ 1 := by
    intro h
    apply hb
    have hmem : a u ∈ U := hu.symm ▸ hzU
    simpa only [h, Path.target] using hmem
  let tail : Path z b := (a.subpath u 1).cast hu.symm a.target.symm
  have htail : range tail ⊆ range a := by
    rw [show range tail = range (a.subpath u 1) from rfl,
      Path.range_subpath_of_le a u 1 le_top]
    exact image_subset_range _ _
  have htailinj : Function.Injective tail := by
    intro s t h
    have heq := congrArg Subtype.val (ha h)
    simp only [Set.Icc.coe_convexComb] at heq
    norm_num at heq
    have hu' : (u : ℝ) ≠ 1 := fun h => hu1 (Subtype.ext h)
    apply Subtype.ext
    have hmul : ((s : ℝ) - t) * (1 - (u : ℝ)) = 0 := by nlinarith [heq]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hu'.symm))
  have hmeet : range w ∩ range tail = {z} := by
    apply subset_antisymm
    · exact (inter_subset_inter_right _ htail).trans hwmeet.le
    · exact singleton_subset_iff.mpr ⟨w.target_mem_range, tail.source_mem_range⟩
  let v' : Path r b := w.trans tail
  have hv'inj : Function.Injective v' := LatticeProb.Topology.path_trans_injective hw htailinj hmeet
  have hv'sub : range v' ⊆ (U ∪ {b}) \ S := by
    rw [show range v' = range w ∪ range tail from Path.trans_range w tail]
    rintro y (hy | hy)
    · have hy' := hvU (by simpa only [Path.symm_range] using hwsub hy)
      exact ⟨Or.inl hy'.1, hy'.2⟩
    · have hya := htail hy
      refine ⟨?_, fun hs => disjoint_left.mp haS hya hs⟩
      obtain ⟨t, rfl⟩ := hya
      by_cases ht : t = 1
      · exact Or.inr (by simp only [ht, Path.target, mem_singleton_iff])
      · exact Or.inl (haU t ht)
  have hv'K : range v' ∩ K = {r} := by
    apply subset_antisymm
    · rintro y ⟨hy, hyK⟩
      rw [show range v' = range w ∪ range tail from Path.trans_range w tail] at hy
      rcases hy with hy | hy
      · have hyv : y ∈ range v := by simpa only [Path.symm_range] using hwsub hy
        rw [← hvK]
        exact ⟨hyv, hyK⟩
      · exact (disjoint_left.mp haK (htail hy) (Or.inl hyK)).elim
    · exact singleton_subset_iff.mpr ⟨v'.source_mem_range, hrK⟩
  have htailv : range (a.subpath u 1) ⊆ range v' := by
    intro y hy
    rw [show range v' = range w ∪ range tail from Path.trans_range w tail]
    exact Or.inr hy
  obtain ⟨w', hw', hw'sub, t, ht, hspeed⟩ :=
    exists_path_with_parametrized_retained_tail v' a hv'inj ha hu1 htailv
  refine ⟨w', hw', hw'sub.trans hv'sub, ?_, t, ht, hspeed⟩
  apply subset_antisymm
  · exact (inter_subset_inter_left _ hw'sub).trans hv'K.le
  · exact singleton_subset_iff.mpr ⟨w'.source_mem_range, hrK⟩

end FiniteAvalanches.Electrical.StatementGeometry
