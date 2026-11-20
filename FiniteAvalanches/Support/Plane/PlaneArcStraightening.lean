import FiniteAvalanches.Support.Plane.ArcClosingPath
import FiniteAvalanches.Support.Plane.ArcEndpointAccess

/-!
# Injective access to the endpoints of simple arcs

Every endpoint of a simple plane arc is reached from its complement by an
injective path. The parameter-preserving whole-plane straightening of simple
arcs is proved in `ArcClosingPath`.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

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
