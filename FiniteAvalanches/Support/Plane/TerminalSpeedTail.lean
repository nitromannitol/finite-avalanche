import FiniteAvalanches.Support.Plane.CommonEndpointTripod

/-!
# Terminal subpaths from prescribed speed

A parametrized terminal agreement contains the corresponding terminal subarc.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- Exact terminal speed implies inclusion of the corresponding terminal
subpath in the reparametrized path. -/
theorem terminal_subpath_subset_of_speed {X : Type*} [TopologicalSpace X]
    {r x y : X} (w : Path r y) (p : Path x y) (t : unitInterval)
    (hspeed : ∀ (u : unitInterval) (hu : ((t : ℝ) + 1) / 2 ≤ (u : ℝ)),
      w u = p ⟨2 * (u : ℝ) - 1, by constructor <;> linarith [t.property.1, u.property.2]⟩) :
    range (p.subpath t 1) ⊆ range w := by
  rw [Path.range_subpath_of_le p t 1 le_top]
  rintro z ⟨v, hv, rfl⟩
  let u : unitInterval := ⟨((v : ℝ) + 1) / 2, by constructor <;> linarith [v.property.1, v.property.2]⟩
  have hu : ((t : ℝ) + 1) / 2 ≤ (u : ℝ) := by
    change ((t : ℝ) + 1) / 2 ≤ ((v : ℝ) + 1) / 2
    have h : (t : ℝ) ≤ v := hv.1
    linarith
  refine ⟨u, ?_⟩
  rw [hspeed u hu]
  congr 1
  apply Subtype.ext
  change 2 * (((v : ℝ) + 1) / 2) - 1 = (v : ℝ)
  ring

end FiniteAvalanches.Electrical.StatementGeometry
