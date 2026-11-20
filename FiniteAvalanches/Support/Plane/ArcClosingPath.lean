import FiniteAvalanches.Support.Plane.InfiniteEndpointPath
import FiniteAvalanches.Support.Plane.PathArcExtraction
import FiniteAvalanches.Support.Plane.ArcStraightHomeomorph
import FiniteAvalanches.Support.Plane.ArcRemoval

/-!
# Closing a plane arc and straightening it

The complement of a simple plane arc supplies a closing path which meets the
arc only at its endpoints. An injective path inside it closes the arc into a
Jordan curve, and the relative Jordan–Schönflies theorem produces a
parameter-preserving plane homeomorphism onto the horizontal unit segment.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

/-- A simple plane arc has a closing path meeting it only at its endpoints. -/
theorem exists_closing_path_of_injective_path
    {x y : ℝ × ℝ} (p : Path x y) (hp : Function.Injective p) :
    ∃ q : Path x y, range p ∩ range q = {x, y} := by
  obtain ⟨a, q, hq⟩ := exists_path_to_arc_endpoint p hp
  have hp' : Function.Injective p.symm := hp.comp unitInterval.symm_involutive.injective
  obtain ⟨b, r, hr'⟩ := exists_path_to_arc_endpoint p.symm hp'
  have hr : ∀ t : unitInterval, t ≠ 1 → r t ∉ range p := by
    simpa only [Path.symm_range] using hr'
  have ha : a ∉ range p := by simpa only [Path.source] using hq 0 (by norm_num)
  have hb : b ∉ range p := by simpa only [Path.source] using hr 0 (by norm_num)
  let U := (range p)ᶜ
  have hU : IsOpen U := (isCompact_range p.continuous).isClosed.isOpen_compl
  have hconn : IsPreconnected U := by
    simpa only [U, Set.sdiff_eq, Set.univ_inter] using
      (isPreconnected_sdiff_injective_path isOpen_univ isPreconnected_univ p hp
        (subset_univ (range p)))
  have hpath : IsPathConnected U := hU.isConnected_iff_isPathConnected.mp ⟨⟨a, ha⟩, hconn⟩
  obtain ⟨w, hw⟩ := hpath.joinedIn a ha b hb
  let s : Path x y := q.symm.trans (w.trans r)
  refine ⟨s, ?_⟩
  ext z
  simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hzp, hzs⟩
    change z ∈ range (q.symm.trans (w.trans r)) at hzs
    rw [Path.trans_range, Path.trans_range, Path.symm_range] at hzs
    rcases hzs with hzq | hzw | hzr
    · obtain ⟨t, rfl⟩ := hzq
      have ht : t = 1 := by
        by_contra ht
        exact hq t ht hzp
      left
      simp only [ht, Path.target]
    · obtain ⟨t, rfl⟩ := hzw
      exact ((hw t) hzp).elim
    · obtain ⟨t, rfl⟩ := hzr
      have ht : t = 1 := by
        by_contra ht
        exact hr t ht hzp
      right
      simp only [ht, Path.target]
  · rintro (rfl | rfl)
    · exact ⟨p.source_mem_range, s.source_mem_range⟩
    · exact ⟨p.target_mem_range, s.target_mem_range⟩

/-- Every simple plane arc has a simple complementary closing arc. -/
theorem exists_simple_closing_arc_of_injective_path
    {x y : ℝ × ℝ} (p : Path x y) (hp : Function.Injective p) :
    ∃ q : Path x y, Function.Injective q ∧ range p ∩ range q = {x, y} := by
  have hxy : x ≠ y := by
    intro h
    have h01 : (0 : unitInterval) = 1 := hp (by simpa only [Path.source, Path.target] using h)
    norm_num at h01
  obtain ⟨r, hr⟩ := exists_closing_path_of_injective_path p hp
  obtain ⟨q, hq, hqr⟩ := exists_injective_path_in_range r hxy
  refine ⟨q, hq, ?_⟩
  apply Set.Subset.antisymm
  · exact (inter_subset_inter_right _ hqr).trans (le_of_eq hr)
  · simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨⟨p.source_mem_range, q.source_mem_range⟩,
      ⟨p.target_mem_range, q.target_mem_range⟩⟩

/-- Every simple plane arc admits a parameter-preserving plane homeomorphism
to the horizontal unit segment. -/
theorem exists_plane_homeomorph_straightening
    {x y : ℝ × ℝ} (p : Path x y) (hp : Function.Injective p) :
    ∃ F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), ∀ t : unitInterval, F (p t) = (t.val, 0) := by
  obtain ⟨q, hq, hmeet⟩ := exists_simple_closing_arc_of_injective_path p hp
  exact exists_plane_homeomorph_straightening_of_closing_arc p q hp hq hmeet

end FiniteAvalanches.Electrical.StatementGeometry
