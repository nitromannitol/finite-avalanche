import FiniteAvalanches.Support.Plane.LoopPathReduction
import Mathlib.Topology.MetricSpace.Perfect

/-!
# Residual points of a loop cancellation

For a maximal loop cancellation, endpoints remain outside every loop interior
and no interior residual point is isolated.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set
open scoped Topology

/-- The points not belonging to the interior of any cancelled loop. -/
def loopResidual (S : Set (unitInterval × unitInterval)) : Set unitInterval :=
  {t | ∀ v ∈ S, t ∉ Ioo v.1 v.2}

/-- The residual of a family of loop interiors is closed. -/
theorem isClosed_loopResidual (S : Set (unitInterval × unitInterval)) :
    IsClosed (loopResidual S) := by
  have heq : loopResidual S = (⋃ v ∈ S, Ioo v.1 v.2)ᶜ := by
    ext t
    simp only [loopResidual, mem_setOf_eq, mem_compl_iff, mem_iUnion, not_exists]
  rw [heq]
  exact (isOpen_iUnion fun v => isOpen_iUnion fun _ => isOpen_Ioo).isClosed_compl

/-- Both endpoints of each maximal cancelled loop are residual. -/
theorem IsLoopCancellation.endpoints_mem_loopResidual_of_maximal
    {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y)
    {S : Set (unitInterval × unitInterval)} (hS : IsLoopCancellation p S)
    (hmax : ∀ T, IsLoopCancellation p T → LoopFamilyRefines S T → LoopFamilyRefines T S)
    {v : unitInterval × unitInterval} (hv : v ∈ S) :
    v.1 ∈ loopResidual S ∧ v.2 ∈ loopResidual S := by
  constructor <;> intro w hw hmem
  · by_cases heq : v = w
    · subst w
      exact (lt_irrefl v.1) hmem.1
    · rcases hS.separated_of_maximal p hmax hv hw heq with hlt | hlt
      · exact (not_lt_of_ge ((hS.1 v hv).1.le.trans hlt.le)) hmem.1
      · exact (not_lt_of_ge hlt.le) hmem.2
  · by_cases heq : v = w
    · subst w
      exact (lt_irrefl v.2) hmem.2
    · rcases hS.separated_of_maximal p hmax hv hw heq with hlt | hlt
      · exact (not_lt_of_ge hlt.le) hmem.1
      · exact (not_lt_of_ge (hlt.le.trans (hS.1 v hv).1.le)) hmem.2

/-- No residual point strictly inside the parameter interval is isolated. -/
theorem IsLoopCancellation.residual_not_isolated_of_maximal
    {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y)
    {S : Set (unitInterval × unitInterval)} (hS : IsLoopCancellation p S)
    (hmax : ∀ T, IsLoopCancellation p T → LoopFamilyRefines S T → LoopFamilyRefines T S)
    {z l r : unitInterval} (hz : z ∈ loopResidual S) (hl : l < z) (hr : z < r) :
    ∃ t ∈ loopResidual S, t ∈ Ioo l r ∧ t ≠ z := by
  classical
  by_contra hnone
  have hbad : ∀ t ∈ loopResidual S, t ∈ Ioo l r → t = z := by
    intro t htF htlr
    by_contra hne
    exact hnone ⟨t, htF, htlr, hne⟩
  obtain ⟨a, hla, haz⟩ := exists_between hl
  obtain ⟨b, hzb, hbr⟩ := exists_between hr
  have haF : a ∉ loopResidual S := by
    intro ha
    exact (ne_of_lt haz) (hbad a ha ⟨hla, lt_trans haz hr⟩)
  have hbF : b ∉ loopResidual S := by
    intro hb
    exact (ne_of_gt hzb) (hbad b hb ⟨lt_trans hl hzb, hbr⟩)
  have haLoop : ∃ v ∈ S, a ∈ Ioo v.1 v.2 := by
    by_contra h
    apply haF
    intro v hv hav
    exact h ⟨v, hv, hav⟩
  have hbLoop : ∃ w ∈ S, b ∈ Ioo w.1 w.2 := by
    by_contra h
    apply hbF
    intro w hw hbw
    exact h ⟨w, hw, hbw⟩
  obtain ⟨v, hv, hav⟩ := haLoop
  obtain ⟨w, hw, hbw⟩ := hbLoop
  have hvz : v.2 ≤ z := by
    by_contra h
    exact hz v hv ⟨lt_trans hav.1 haz, lt_of_not_ge h⟩
  have hzw : z ≤ w.1 := by
    by_contra h
    exact hz w hw ⟨lt_of_not_ge h, lt_trans hzb hbw.2⟩
  have hv2 : v.2 = z := by
    apply hbad v.2 (hS.endpoints_mem_loopResidual_of_maximal p hmax hv).2
    exact ⟨lt_trans hla hav.2, lt_of_le_of_lt hvz hr⟩
  have hw1 : w.1 = z := by
    apply hbad w.1 (hS.endpoints_mem_loopResidual_of_maximal p hmax hw).1
    exact ⟨lt_of_lt_of_le hl hzw, lt_trans hbw.1 hbr⟩
  exact hS.not_adjacent_of_maximal p hmax hv hw (hv2.trans hw1.symm)

/-- The closure of the interior residual points of a maximal cancellation is
perfect. -/
theorem IsLoopCancellation.perfect_interior_loopResidual_of_maximal
    {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y)
    {S : Set (unitInterval × unitInterval)} (hS : IsLoopCancellation p S)
    (hmax : ∀ T, IsLoopCancellation p T → LoopFamilyRefines S T → LoopFamilyRefines T S) :
    Perfect (closure (loopResidual S ∩ Ioo 0 1)) := by
  apply Preperfect.perfect_closure
  rw [preperfect_iff_nhds]
  intro z hz U hU
  have hz0 : (0 : unitInterval) < z := hz.2.1
  have hz1 : z < (1 : unitInterval) := hz.2.2
  obtain ⟨l, hlz, hlU⟩ := exists_Ioc_subset_of_mem_nhds hU ⟨0, hz0⟩
  obtain ⟨r, hzr, hrU⟩ := exists_Ico_subset_of_mem_nhds hU ⟨1, hz1⟩
  obtain ⟨l', hll', hl'z⟩ := exists_between (max_lt hlz hz0)
  obtain ⟨r', hzr', hr'r⟩ := exists_between (lt_min hzr hz1)
  obtain ⟨t, htF, ht, htne⟩ := hS.residual_not_isolated_of_maximal p hmax hz.1 hl'z hzr'
  have htU : t ∈ U := by
    by_cases htz : t ≤ z
    · exact hlU ⟨lt_trans (lt_of_le_of_lt (le_max_left _ _) hll') ht.1, htz⟩
    · exact hrU ⟨le_of_not_ge htz, lt_trans ht.2
        (lt_of_lt_of_le hr'r (min_le_left _ _))⟩
  have ht0 : (0 : unitInterval) < t :=
    lt_trans (lt_of_le_of_lt (le_max_right _ _) hll') ht.1
  have ht1 : t < (1 : unitInterval) :=
    lt_trans ht.2 (lt_of_lt_of_le hr'r (min_le_right _ _))
  exact ⟨t, ⟨htU, htF, ht0, ht1⟩, htne⟩

/-- A non-loop path has an interior residual parameter in every maximal loop
cancellation. -/
theorem IsLoopCancellation.interior_loopResidual_nonempty_of_maximal
    {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y) (hxy : x ≠ y)
    {S : Set (unitInterval × unitInterval)} (hS : IsLoopCancellation p S)
    (hmax : ∀ T, IsLoopCancellation p T → LoopFamilyRefines S T → LoopFamilyRefines T S) :
    (loopResidual S ∩ Ioo 0 1).Nonempty := by
  classical
  by_contra hnone
  let m : unitInterval := ⟨1 / 2, by norm_num⟩
  have hm : m ∉ loopResidual S := by
    intro hmF
    apply hnone
    refine ⟨m, hmF, ?_⟩
    change (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1
    norm_num
  have hex : ∃ v ∈ S, m ∈ Ioo v.1 v.2 := by
    by_contra h
    apply hm
    intro v hv hmv
    exact h ⟨v, hv, hmv⟩
  obtain ⟨v, hv, _⟩ := hex
  have hvF := hS.endpoints_mem_loopResidual_of_maximal p hmax hv
  have hv0 : v.1 = 0 := by
    by_contra hne
    have hvpos : (0 : unitInterval) < v.1 := lt_of_le_of_ne bot_le (Ne.symm hne)
    have hvlt : v.1 < (1 : unitInterval) := lt_of_lt_of_le (hS.1 v hv).1 le_top
    exact hnone ⟨v.1, hvF.1, hvpos, hvlt⟩
  have hv1 : v.2 = 1 := by
    by_contra hne
    have hvpos : (0 : unitInterval) < v.2 := lt_of_le_of_lt bot_le (hS.1 v hv).1
    have hvlt : v.2 < (1 : unitInterval) := lt_of_le_of_ne le_top hne
    exact hnone ⟨v.2, hvF.2, hvpos, hvlt⟩
  apply hxy
  simpa only [hv0, hv1, Path.source, Path.target] using (hS.1 v hv).2

/-- An open interval avoiding the perfect residual core is contained in one
closed cancelled-loop interval. -/
theorem IsLoopCancellation.exists_loop_of_disjoint_residual_core
    {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y)
    {S : Set (unitInterval × unitInterval)} (hS : IsLoopCancellation p S)
    (hmax : ∀ T, IsLoopCancellation p T → LoopFamilyRefines S T → LoopFamilyRefines T S)
    {s t : unitInterval} (hst : s < t)
    (hdisj : Disjoint (Ioo s t) (closure (loopResidual S ∩ Ioo 0 1))) :
    ∃ v ∈ S, v.1 ≤ s ∧ t ≤ v.2 := by
  classical
  obtain ⟨m, hsm, hmt⟩ := exists_between hst
  have hmF : m ∉ loopResidual S := by
    intro hm
    have hmcore : m ∈ closure (loopResidual S ∩ Ioo 0 1) :=
      subset_closure ⟨hm, lt_of_le_of_lt bot_le hsm, lt_of_lt_of_le hmt le_top⟩
    exact Set.disjoint_left.mp hdisj ⟨hsm, hmt⟩ hmcore
  have hex : ∃ v ∈ S, m ∈ Ioo v.1 v.2 := by
    by_contra h
    apply hmF
    intro v hv hmv
    exact h ⟨v, hv, hmv⟩
  obtain ⟨v, hv, hmv⟩ := hex
  have hvF := hS.endpoints_mem_loopResidual_of_maximal p hmax hv
  refine ⟨v, hv, ?_, ?_⟩
  · by_contra h
    have hsv : s < v.1 := lt_of_not_ge h
    have hvcore : v.1 ∈ closure (loopResidual S ∩ Ioo 0 1) :=
      subset_closure ⟨hvF.1, lt_of_le_of_lt bot_le hsv, lt_of_lt_of_le
        (lt_trans hmv.1 hmt) le_top⟩
    exact Set.disjoint_left.mp hdisj ⟨hsv, lt_trans hmv.1 hmt⟩ hvcore
  · by_contra h
    have hvt : v.2 < t := lt_of_not_ge h
    have hvcore : v.2 ∈ closure (loopResidual S ∩ Ioo 0 1) :=
      subset_closure ⟨hvF.2, lt_of_le_of_lt bot_le (lt_trans hsm hmv.2),
        lt_of_lt_of_le hvt le_top⟩
    exact Set.disjoint_left.mp hdisj ⟨lt_trans hsm hmv.2, hvt⟩ hvcore

end FiniteAvalanches.Electrical.StatementGeometry
