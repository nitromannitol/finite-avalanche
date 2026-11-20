import FiniteAvalanches.Support.Plane.TreePaths

/-!
# Joining boundary accesses with prescribed tails

Two disjoint boundary accesses can be joined by a simple path that retains a
terminal subarc of each access.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- Two disjoint boundary access paths can be joined while retaining a terminal
subpath of each and avoiding a prescribed finite set. -/
theorem exists_injective_path_between_boundary_accesses_with_tails
    {U S : Set (ℝ × ℝ)} {a b c d : ℝ × ℝ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (p : Path a b) (q : Path c d) (hp : Function.Injective p)
    (hq : Function.Injective q) (hd : Disjoint (range p) (range q))
    (hpU : ∀ t : unitInterval, t ≠ 1 → p t ∈ U)
    (hqU : ∀ t : unitInterval, t ≠ 1 → q t ∈ U)
    (hb : b ∉ U) (hd' : d ∉ U)
    (hS : S.Finite) (hpS : Disjoint (range p) S) (hqS : Disjoint (range q) S) :
    ∃ w : Path d b, Function.Injective w ∧ Disjoint (range w) S ∧
      range w ∩ Uᶜ = {d, b} ∧
      (∃ t : unitInterval, t ≠ 1 ∧ range (p.subpath t 1) ⊆ range w) ∧
      (∃ t : unitInterval, t ≠ 1 ∧ range (q.subpath t 1) ⊆ range w) := by
  classical
  let paths : Unit → Path c d := fun _ => q
  have haU : a ∈ U := by simpa only [Path.source] using hpU 0 (by norm_num)
  have haP : a ∈ range p := p.source_mem_range
  have haQ : a ∉ range q := fun h => disjoint_left.mp hd haP h
  have haS : a ∉ S := fun h => disjoint_left.mp hpS haP h
  have hr : a ∈ (U \ (⋃ i ∈ ({()} : Finset Unit), range (paths i))) \ S := by
    refine ⟨⟨haU, ?_⟩, haS⟩
    simpa [paths] using haQ
  obtain ⟨v, hv, hvS, hvboundary, _, t, ht, htail⟩ :=
    exists_path_to_boundary_avoiding_paths_disjoint_inside_and_finite
      hU hconn ({()} : Finset Unit) paths
      (by simpa [paths] using hq) (by simp)
      (by simpa [paths] using hqU) (by simpa [paths] using hd')
      hS (by simpa [paths] using hqS) hr (i := ()) (by simp)
  have hvrev : Function.Injective v.symm := by
    intro x y h
    exact unitInterval.symm_involutive.injective (hv h)
  have hdP : d ∉ range p := fun h => disjoint_left.mp hd h q.target_mem_range
  obtain ⟨z, hz, w, hw, hwsub, hwmeet, T, hT, hrange⟩ :=
    exists_initial_path_first_hit_with_subpath v.symm hvrev
      (isCompact_range p.continuous).isClosed hdP haP
  have hzU : z ∈ U := by
    by_contra hzU
    have hzv : z ∈ range v := by simpa only [Path.symm_range] using hwsub w.target_mem_range
    have hz' : z ∈ ({d} : Set (ℝ × ℝ)) := hvboundary ▸ ⟨hzv, hzU⟩
    exact hdP (mem_singleton_iff.mp hz' ▸ hz)
  obtain ⟨u, hu⟩ := hz
  have hu1 : u ≠ 1 := by
    intro heq
    apply hb
    rw [← hu, heq, Path.target] at hzU
    exact hzU
  let tail : Path z b := (p.subpath u 1).cast hu.symm p.target.symm
  have htailP : range tail ⊆ range p := by
    rw [show range tail = range (p.subpath u 1) from rfl, Path.range_subpath]
    exact image_subset_range _ _
  have htailinj : Function.Injective tail := by
    intro x y h
    have hv' := congrArg Subtype.val (hp h)
    simp only [Set.Icc.coe_convexComb] at hv'
    norm_num at hv'
    have hu' : (u : ℝ) ≠ 1 := fun h => hu1 (Subtype.ext h)
    apply Subtype.ext
    have hz' : ((x : ℝ) - y) * (1 - (u : ℝ)) = 0 := by nlinarith [hv']
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz').resolve_right (sub_ne_zero.mpr hu'.symm))
  have hmeet : range w ∩ range tail = {z} := by
    apply subset_antisymm
    · exact (inter_subset_inter_right _ htailP).trans hwmeet.le
    · exact singleton_subset_iff.mpr ⟨w.target_mem_range, tail.source_mem_range⟩
  refine ⟨w.trans tail, LatticeProb.Topology.path_trans_injective hw htailinj hmeet, ?_, ?_, ?_, ?_⟩
  · rw [Path.trans_range]
    exact disjoint_union_left.mpr ⟨hvS.mono_left (by simpa using hwsub), hpS.mono_left htailP⟩
  · rw [Path.trans_range, union_inter_distrib_right]
    have hwboundary : range w ∩ Uᶜ ⊆ {d} := by
      exact (inter_subset_inter_left _ (by simpa using hwsub)).trans hvboundary.le
    have htboundary : range tail ∩ Uᶜ ⊆ {b} := by
      intro x hx
      obtain ⟨s, hs⟩ := htailP hx.1
      have hs1 : s = 1 := by
        by_contra h
        exact hx.2 (hs ▸ hpU s h)
      simpa only [hs1, Path.target, mem_singleton_iff] using hs.symm
    apply subset_antisymm
    · exact union_subset_union hwboundary htboundary
    · intro x hx
      simp only [mem_insert_iff, mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Or.inl ⟨w.source_mem_range, hd'⟩
      · exact Or.inr ⟨tail.target_mem_range, hb⟩
  · exact ⟨u, hu1, fun x hx => by
      rw [Path.trans_range]
      exact Or.inr hx⟩
  · obtain ⟨t', ht', htail'⟩ := terminal_subpath_in_initial_reverse v q hv ht hT htail
    exact ⟨t', ht', fun x hx => by
      rw [Path.trans_range]
      exact Or.inl (hrange ▸ htail' hx)⟩

end FiniteAvalanches.Electrical.StatementGeometry
