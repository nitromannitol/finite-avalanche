import FiniteAvalanches.Support.Plane.DiskBoundaryImage
import FiniteAvalanches.Support.Plane.PlaneArcStraightening

/-!
# Stable orientation and Jordan disk images

Oriented realization of all plane-homeomorphic Jordan disk boundaries is
equivalent to the isotopy dichotomy for plane homeomorphisms. The dichotomy
also supplies parametrized straightening of every simple plane arc.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set Filter
open scoped Topology
open FiniteAvalanches.Electrical.Source

noncomputable section

/-- The standard disk is a neighborhood of the origin. -/
theorem complexDisk_mem_nhds_zero : complexDisk ∈ 𝓝 (0 : Plane) := by
  let U : Set Plane := {x | ‖Complex.equivRealProdCLM.symm x‖ < 2}
  have hU : IsOpen U := isOpen_lt (continuous_norm.comp Complex.equivRealProdCLM.symm.continuous)
    continuous_const
  have h0 : (0 : Plane) ∈ U := by simp [U]
  apply mem_of_superset (hU.mem_nhds h0)
  intro x hx
  exact (mem_complexDisk x).2 (le_of_lt hx)

/-- Universal oriented realization of Jordan disk boundaries is equivalent to
isotopy to the identity after at most a reflection of the domain. -/
theorem oriented_boundary_realization_iff_stable_orientation :
    (∀ f : Plane ≃ₜ Plane, ∃ c : OrientedChart,
      c.map '' frontier complexDisk = f '' frontier complexDisk) ↔
    (∀ f : Plane ≃ₜ Plane,
      (∃ c : OrientedChart, c.map = f) ∨
      (∃ c : OrientedChart, c.map = planeReflection.trans f)) := by
  constructor
  · intro h f
    obtain ⟨c, hc⟩ := h f
    have hd := image_complexDisk_eq_of_image_frontier_eq c.map f hc
    rcases exists_orientedChart_agree_on_complexDisk_of_image f c hd with h | h
    · obtain ⟨d, hd⟩ := h
      have hloc : f =ᶠ[𝓝 (0 : Plane)] d.map := by
        filter_upwards [complexDisk_mem_nhds_zero] with x hx
        exact (hd x hx).symm
      exact Or.inl ⟨orientedChartOfLocallyEq f d 0 hloc, rfl⟩
    · obtain ⟨d, hd⟩ := h
      have hloc : planeReflection.trans f =ᶠ[𝓝 (0 : Plane)] d.map := by
        filter_upwards [complexDisk_mem_nhds_zero] with x hx
        exact (hd x hx).symm
      exact Or.inr ⟨orientedChartOfLocallyEq (planeReflection.trans f) d 0 hloc, rfl⟩
  · intro h f
    rcases h f with ⟨c, hc⟩ | ⟨c, hc⟩
    · exact ⟨c, by rw [hc]⟩
    · refine ⟨c, ?_⟩
      rw [hc]
      change (f ∘ planeReflection) '' frontier complexDisk = f '' frontier complexDisk
      rw [image_comp, image_frontier_complexDisk planeReflection planeReflection_image_complexDisk]

/-- Oriented realization of plane-homeomorphic disk boundaries implies
parametrized oriented straightening of every simple plane arc. -/
theorem exists_orientedChart_straightening_of_universal_boundary_realization
    (h : ∀ f : Plane ≃ₜ Plane, ∃ c : OrientedChart,
      c.map '' frontier complexDisk = f '' frontier complexDisk)
    (gamma : unitInterval → Plane) (hc : Continuous gamma) (hi : Function.Injective gamma) :
    ∃ c : OrientedChart, ∀ t, c.map (gamma t) = (t.val, 0) := by
  let p : Path (gamma 0) (gamma 1) := ⟨⟨gamma, hc⟩, rfl, rfl⟩
  obtain ⟨f, hf⟩ := exists_plane_homeomorph_straightening p hi
  obtain ⟨c, hboundary⟩ := h f.symm
  exact exists_orientedChart_straightening_of_boundary_image gamma f hf c hboundary

end
end FiniteAvalanches.Electrical.StatementGeometry
