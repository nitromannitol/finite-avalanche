import FiniteAvalanches.Support.Plane.ArcStraightHomeomorph
import FiniteAvalanches.Support.Plane.BoundaryArcJoin

/-!
# Straightening a plane arc from endpoint accesses

Disjoint accesses to the endpoints in the complement of a simple arc give a
closing arc and hence a parameter-preserving homeomorphism of the plane.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

/-- A simple plane arc with disjoint endpoint accesses in its complement admits
parameter-preserving straightening by a homeomorphism of the plane. -/
theorem exists_plane_homeomorph_straightening_of_endpoint_accesses
    {x y a b : ℝ × ℝ} (p : Path x y) (hp : Function.Injective p)
    (q : Path a x) (r : Path b y) (hq : Function.Injective q)
    (hr : Function.Injective r) (hdisj : Disjoint (range q) (range r))
    (hqout : ∀ t : unitInterval, t ≠ 1 → q t ∉ range p)
    (hrout : ∀ t : unitInterval, t ≠ 1 → r t ∉ range p) :
    ∃ F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), ∀ t : unitInterval, F (p t) = (t.val, 0) := by
  let U := (range p)ᶜ
  have hU : IsOpen U := (isCompact_range p.continuous).isClosed.isOpen_compl
  have hconn : IsPreconnected U := by
    simpa only [U, Set.sdiff_eq, Set.univ_inter] using
      (isPreconnected_sdiff_injective_path isOpen_univ isPreconnected_univ p hp
        (subset_univ (range p)))
  have hx : x ∉ U := fun h => h p.source_mem_range
  have hy : y ∉ U := fun h => h p.target_mem_range
  obtain ⟨s, hs, hmeet⟩ := exists_injective_path_between_boundary_accesses hU hconn
    q r hq hr hdisj hqout hrout hx hy
  have hmeet' : range p ∩ range s = {x, y} := by
    simpa only [U, compl_compl, inter_comm] using hmeet
  exact exists_plane_homeomorph_straightening_of_closing_arc p s hp hs hmeet'

end FiniteAvalanches.Electrical.StatementGeometry
