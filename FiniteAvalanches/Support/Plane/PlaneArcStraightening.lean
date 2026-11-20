import FiniteAvalanches.Support.Plane.PathArcExtraction

/-!
# Whole-plane straightening of simple arcs

Endpoint access, loop deletion, and the relative Jordan–Schönflies theorem
produce a parameter-preserving plane homeomorphism for any simple arc.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

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

/-- Every endpoint of a simple plane arc is accessible from its complement by
an injective path. -/
theorem exists_injective_path_to_arc_endpoint
    {x y : ℝ × ℝ} (p : Path x y) (hp : Function.Injective p) :
    ∃ a : ℝ × ℝ, ∃ q : Path a x, Function.Injective q ∧
      ∀ t : unitInterval, t ≠ 1 → q t ∉ range p := by
  obtain ⟨a, q, hqout⟩ := exists_path_to_arc_endpoint p hp
  have hax : a ≠ x := by
    intro heq
    have ha : a ∉ range p := by simpa only [Path.source] using hqout 0 (by norm_num)
    exact ha (heq ▸ p.source_mem_range)
  obtain ⟨r, hr, hrq⟩ := exists_injective_path_in_range q hax
  refine ⟨a, r, hr, ?_⟩
  intro t ht hmem
  obtain ⟨u, hu⟩ := hrq ⟨t, rfl⟩
  have hu1 : u = 1 := by
    by_contra hu1
    exact hqout u hu1 (hu ▸ hmem)
  have hrt : r t = x := by simpa only [hu1, Path.target] using hu.symm
  apply ht
  apply hr
  simpa only [Path.target] using hrt

end FiniteAvalanches.Electrical.StatementGeometry
