import FiniteAvalanches.Electrical.Plane.DirectedPaths
import Mathlib.Order.Interval.Finset.Basic

/-! Exact interval coverage and disjointness along an actual increasing copied path. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical

/-- Every height above the start and at most the end belongs to an actual path-copy interval. -/
theorem ForwardPath.interval_cover {V E : Type*} {a b : E → V} (H : V → ℝ)
    {x y : V} (p : ForwardPath a b x y)
    (hi : ∀ e ∈ p.edges, H (a e) < H (b e)) :
    ∀ u, H x < u → u ≤ H y → ∃ e ∈ p.edges, H (a e) ≤ u ∧ u ≤ H (b e) := by
  induction p with
  | nil x => intro u hxu huy; exact (not_lt_of_ge huy hxu).elim
  | cons e p ih =>
    intro u hxu huy
    by_cases hue : u ≤ H (b e)
    · exact ⟨e,List.mem_cons_self,hxu.le,hue⟩
    · obtain ⟨f,hf,huf⟩ := ih (fun z hz => hi z (List.mem_cons_of_mem _ hz)) u (lt_of_not_ge hue) huy
      exact ⟨f,List.mem_cons_of_mem _ hf,huf⟩

/-- The start height is also covered whenever the path has distinct endpoints. -/
theorem ForwardPath.closed_interval_cover {V E : Type*} {a b : E → V} (H : V → ℝ)
    {x y : V} (p : ForwardPath a b x y) (hne : x ≠ y)
    (hi : ∀ e ∈ p.edges, H (a e) < H (b e)) :
    ∀ u, H x ≤ u → u ≤ H y → ∃ e ∈ p.edges, H (a e) ≤ u ∧ u ≤ H (b e) := by
  intro u hxu huy
  by_cases hxe : H x = u
  · cases p with
    | nil x => exact (hne rfl).elim
    | cons e p =>
      exact ⟨e,List.mem_cons_self,by rw [hxe],by rw [← hxe]; exact (hi e List.mem_cons_self).le⟩
  · exact p.interval_cover H hi u (lt_of_le_of_ne hxu hxe) huy

/-- Distinct copies along the path have disjoint open stream intervals. -/
theorem ForwardPath.interval_disjoint {V E : Type*} {a b : E → V} (H : V → ℝ)
    {x y : V} (p : ForwardPath a b x y)
    (hi : ∀ e ∈ p.edges, H (a e) < H (b e)) :
    ∀ e ∈ p.edges, ∀ f ∈ p.edges, e ≠ f →
      Disjoint (Set.Ioo (H (a e)) (H (b e))) (Set.Ioo (H (a f)) (H (b f))) := by
  induction p with
  | nil => intro e he; exact (List.not_mem_nil he).elim
  | cons e p ih =>
    have htail : ∀ z ∈ p.edges, H (a z) < H (b z) := fun z hz => hi z (List.mem_cons_of_mem _ hz)
    have he (f : E) (hf : f ∈ p.edges) :
        Disjoint (Set.Ioo (H (a e)) (H (b e))) (Set.Ioo (H (a f)) (H (b f))) := by
      apply Set.disjoint_left.mpr
      intro u hu hv
      exact (not_lt_of_ge ((p.edge_height H htail f hf).trans hv.1.le)) hu.2
    intro f hf g hg hfg
    rcases List.mem_cons.mp hf with rfl | hf
    · rcases List.mem_cons.mp hg with rfl | hg
      · exact (hfg rfl).elim
      · exact he g hg
    · rcases List.mem_cons.mp hg with rfl | hg
      · exact (he f hf).symm
      · exact ih htail f hf g hg hfg

end FiniteAvalanches.Electrical.Plane
