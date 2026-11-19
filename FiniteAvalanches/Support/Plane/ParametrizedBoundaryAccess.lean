import FiniteAvalanches.Support.Plane.CrossingAccess
import FiniteAvalanches.Support.Plane.TerminalReparam

/-!
# Parametrized boundary access

A boundary access path can be chosen to follow a specified terminal arc with
controlled speed while avoiding the other boundary arcs.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb Set unitInterval

/-- A chosen boundary arc admits a simple access path with a prescribed final
parametrization, avoiding the other arcs and a finite set. -/
theorem exists_parametrized_path_to_boundary_avoiding_paths
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
    ∃ w : Path r (y i), Function.Injective w ∧
      Disjoint (range w) S ∧ range w ∩ Uᶜ = {y i} ∧
      Disjoint (range w ∩ U) (⋃ j ∈ s.erase i, range (p j)) ∧
      ∃ u : unitInterval, u ≠ 1 ∧
        ∀ (t : unitInterval) (ht : ((u : ℝ) + 1) / 2 ≤ (t : ℝ)),
          w t = p i ⟨2 * (t : ℝ) - 1, by
            constructor
            · have := u.property.1
              linarith
            · linarith [t.property.2]⟩ := by
  classical
  have hcomp : ∀ j ∈ s, IsPreconnected (range (p j) ∩ Uᶜ) :=
    fun j hj => isPreconnected_range_inter_compl_of_mem_except_target
      (p j) (hinside j hj) (hout j hj)
  have ha : p i 0 ∈ (range (p i) ∩ U) \ S :=
    ⟨⟨⟨0, rfl⟩, hinside i hi 0 (by norm_num)⟩,
      fun h => Set.disjoint_left.mp (hobsS i hi) ⟨0, rfl⟩ h⟩
  obtain ⟨z, ⟨u, hu⟩, q, hq, hqsub, hmeet⟩ :=
    exists_path_first_hit_avoiding_paths_disjoint_inside hU hconn s p hp hd hcomp
      hS hr hi ha
  have hzU : z ∈ U := (hqsub q.target_mem_range).1.1
  have hu1 : u ≠ 1 := by
    intro h
    apply hout i hi
    rw [← hu] at hzU
    simpa only [h, Path.target] using hzU
  let v : Path r (p i u) := q.cast rfl hu
  have hv : Function.Injective v := hq
  have hvsub : range v ⊆ (U \ (⋃ j ∈ s.erase i, range (p j))) \ S := hqsub
  have hvmeet : range v ∩ range (p i) = {p i u} := by
    change range q ∩ range (p i) = {p i u}
    rw [hu]
    exact hmeet
  have htail : Function.Injective ((p i).subpath u 1) := by
    intro a b hab
    have h := congrArg Subtype.val ((hp i hi) hab)
    simp only [Set.Icc.coe_convexComb] at h
    norm_num at h
    have hu' : (u : ℝ) ≠ 1 := fun h => hu1 (Subtype.ext h)
    apply Subtype.ext
    have heq : ((a : ℝ) - b) * (1 - (u : ℝ)) = 0 := by nlinarith [h]
    exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_right (sub_ne_zero.mpr (Ne.symm hu')))
  have htailsub : range ((p i).subpath u 1) ⊆ range (p i) := by
    rw [Path.range_subpath]
    exact image_subset_range _ _
  have hvjoint : range v ∩ range ((p i).subpath u 1) = {p i u} := by
    apply subset_antisymm
    · intro a ha'
      rw [← hvmeet]
      exact ⟨ha'.1, htailsub ha'.2⟩
    · exact singleton_subset_iff.mpr ⟨v.target_mem_range,
        ((p i).subpath u 1).source_mem_range⟩
  have hjoint : Function.Injective (v.trans ((p i).subpath u 1)) :=
    Topology.path_trans_injective hv htail hvjoint
  obtain ⟨w, hw, hwrange, hwt⟩ :=
    path_trans_subpath_reparam_terminal (p i) u hu1 v hjoint
  let w' : Path r (y i) := w.cast rfl (p i).target.symm
  have hw'range : range w' = range v ∪ range ((p i).subpath u 1) := by
    change range w = _
    rw [hwrange, Path.trans_range]
  refine ⟨w', hw, ?_, ?_, ?_, u, hu1, ?_⟩
  · rw [hw'range]
    exact disjoint_union_left.mpr ⟨Set.disjoint_left.mpr (fun _ hz hs => (hvsub hz).2 hs),
      (hobsS i hi).mono_left htailsub⟩
  · rw [hw'range, union_inter_distrib_right]
    have hvU : range v ∩ Uᶜ = ∅ := by
      apply subset_antisymm ?_ (empty_subset _)
      rintro a ⟨ha', haU⟩
      exact haU (hvsub ha').1.1
    rw [hvU, empty_union]
    apply subset_antisymm
    · intro a ha'
      rw [← range_inter_compl_of_mem_except_target (p i) (hinside i hi) (hout i hi)]
      exact ⟨htailsub ha'.1, ha'.2⟩
    · exact singleton_subset_iff.mpr ⟨by
        have h := ((p i).subpath u 1).target_mem_range
        simpa only [Path.target] using h, hout i hi⟩
  · apply Set.disjoint_left.mpr
    rintro a ⟨ha', haU⟩ haobs
    rw [hw'range] at ha'
    rcases ha' with ha' | ha'
    · exact (hvsub ha').1.2 haobs
    · obtain ⟨j, hj, haj⟩ := mem_iUnion₂.mp haobs
      exact Set.disjoint_left.mp (hd i hi j (Finset.mem_of_mem_erase hj)
        (Ne.symm (Finset.mem_erase.mp hj).1)) ⟨htailsub ha', haU⟩ haj
  · exact hwt

end FiniteAvalanches.Electrical.StatementGeometry
