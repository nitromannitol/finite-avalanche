import FiniteAvalanches.Support.Plane.BoundaryTwoStar
import FiniteAvalanches.Support.Plane.TerminalReparam

/-!
# Parametrizing retained tails

A simple path containing a terminal subarc of another simple path can be
shortened and reparametrized to traverse that subarc at a prescribed speed.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- A retained terminal subpath can be traversed with exact speed without
leaving the original simple path. -/
theorem exists_path_with_parametrized_retained_tail
    {X : Type*} [TopologicalSpace X] [T2Space X] {r x y : X}
    (a : Path r y) (p : Path x y) (ha : Function.Injective a)
    (hp : Function.Injective p) {t : unitInterval} (ht : t ≠ 1)
    (hsub : range (p.subpath t 1) ⊆ range a) :
    ∃ w : Path r y, Function.Injective w ∧ range w ⊆ range a ∧
      ∃ u : unitInterval, u ≠ 1 ∧
        ∀ (s : unitInterval) (hs : ((u : ℝ) + 1) / 2 ≤ (s : ℝ)),
          w s = p ⟨2 * (s : ℝ) - 1, by
            constructor
            · have := u.property.1
              linarith
            · linarith [s.property.2]⟩ := by
  let half : unitInterval := ⟨1 / 2, by norm_num⟩
  have hhalf : half ≠ 0 := by
    intro h
    have h' := congrArg Subtype.val h
    norm_num [half] at h'
  obtain ⟨u, hu, htail⟩ := terminal_subpath_in_initial_reverse a p ha ht hhalf hsub
  have hrevsub : range (a.symm.subpath 0 half) ⊆ range a := by
    rw [Path.range_subpath_of_le a.symm 0 half bot_le, ← Path.symm_range a]
    exact image_subset_range _ _
  have hrev : Function.Injective a.symm := by
    intro s v h
    exact unitInterval.symm_involutive.injective (ha h)
  have hr : r ∉ range (p.subpath u 1) := by
    intro hr
    have hr' := htail hr
    rw [Path.range_subpath_of_le a.symm 0 half bot_le] at hr'
    obtain ⟨v, hv, heq⟩ := hr'
    have hv1 : v = 1 := hrev (heq.trans a.symm.target.symm)
    have : (1 : unitInterval) ≤ half := by simpa only [hv1] using hv.2
    have hval : (1 : ℝ) ≤ (1 / 2 : ℝ) := this
    norm_num at hval
  let K := range (p.subpath u 1)
  have hK : IsClosed K := (isCompact_range (p.subpath u 1).continuous).isClosed
  have hyK : y ∈ K := by
    have h := (p.subpath u 1).target_mem_range
    simpa only [Path.target] using h
  obtain ⟨z, hz, q, hq, hqa, hmeet, T, hT, hTq⟩ :=
    exists_initial_path_first_hit_with_subpath a ha hK hr hyK
  have hzne : z ≠ y := by
    intro hzy
    have hyq : y ∈ range q := hzy ▸ q.target_mem_range
    rw [← hTq, Path.range_subpath_of_le a 0 T bot_le] at hyq
    obtain ⟨v, hv, hvy⟩ := hyq
    have hv1 : v = 1 := ha (hvy.trans a.target.symm)
    have hTeq : T = 1 := le_antisymm le_top (by simpa only [hv1] using hv.2)
    have hpuK : p u ∈ K := (p.subpath u 1).source_mem_range
    have hpua : p u ∈ range a := by
      exact hrevsub (htail hpuK)
    have hpuq : p u ∈ range q := by
      rw [← hTq, hTeq, Path.range_subpath_of_le a 0 1 bot_le]
      obtain ⟨v, hv⟩ := hpua
      exact ⟨v, ⟨bot_le, le_top⟩, hv⟩
    have heq : p u = z := mem_singleton_iff.mp (hmeet ▸ ⟨hpuq, hpuK⟩)
    exact hu (hp (heq.trans (hzy.trans p.target.symm)))
  rw [show K = p '' Icc u 1 from Path.range_subpath_of_le p u 1 le_top] at hz hmeet
  obtain ⟨v, hv, hvz⟩ := hz
  have hv1 : v ≠ 1 := by
    intro h
    apply hzne
    simpa only [h, Path.target] using hvz.symm
  let q' : Path r (p v) := q.cast rfl hvz
  have htailinj : Function.Injective (p.subpath v 1) := by
    intro b c h
    have heq := congrArg Subtype.val (hp h)
    simp only [Set.Icc.coe_convexComb] at heq
    norm_num at heq
    have hv' : (v : ℝ) ≠ 1 := fun h => hv1 (Subtype.ext h)
    apply Subtype.ext
    have hz' : ((b : ℝ) - c) * (1 - (v : ℝ)) = 0 := by nlinarith [heq]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz').resolve_right (sub_ne_zero.mpr hv'.symm))
  have htailK : range (p.subpath v 1) ⊆ K := by
    rw [show K = p '' Icc u 1 from Path.range_subpath_of_le p u 1 le_top,
      Path.range_subpath_of_le p v 1 le_top]
    exact image_mono (Icc_subset_Icc hv.1 le_rfl)
  have hjoin : range q' ∩ range (p.subpath v 1) = {p v} := by
    apply subset_antisymm
    · intro b hb
      have hb' : b ∈ range q ∩ p '' Icc u 1 := ⟨hb.1, by simpa only [K, Path.range_subpath_of_le p u 1 le_top] using htailK hb.2⟩
      rw [hmeet] at hb'
      simpa only [hvz] using hb'
    · exact singleton_subset_iff.mpr ⟨q'.target_mem_range, (p.subpath v 1).source_mem_range⟩
  have hinj : Function.Injective (q'.trans (p.subpath v 1)) :=
    LatticeProb.Topology.path_trans_injective hq htailinj hjoin
  obtain ⟨w, hw, hwrange, hspeed⟩ :=
    path_trans_subpath_reparam_terminal p v hv1 q' hinj
  let w' : Path r y := w.cast rfl p.target.symm
  refine ⟨w', hw, ?_, v, hv1, hspeed⟩
  change range w ⊆ range a
  rw [hwrange, Path.trans_range]
  exact union_subset hqa (fun b hb => by
    exact hrevsub (htail (htailK hb)))

end FiniteAvalanches.Electrical.StatementGeometry
