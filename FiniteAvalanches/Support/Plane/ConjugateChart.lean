import FiniteAvalanches.Support.Plane.ArcOrientedReduction

/-!
# Conjugated plane isotopies

Conjugation by an arbitrary plane homeomorphism preserves the existence of a
jointly continuous isotopy and inverse. Local agreement with an oriented chart,
possibly followed by a reflection, suffices for oriented arc straightening.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Filter Set
open scoped Topology
open FiniteAvalanches.Electrical.Source

noncomputable section

/-- Conjugation transports an oriented chart through any plane homeomorphism. -/
def _root_.FiniteAvalanches.Electrical.Source.OrientedChart.conjugate
    (c : OrientedChart) (f : Plane ≃ₜ Plane) : OrientedChart where
  map := f.symm.trans (c.map.trans f)
  isotopy t := f.symm.trans ((c.isotopy t).trans f)
  continuous := f.continuous.comp
    (c.continuous.comp (continuous_fst.prodMk (f.symm.continuous.comp continuous_snd)))
  inverse_continuous := f.continuous.comp
    (c.inverse_continuous.comp (continuous_fst.prodMk (f.symm.continuous.comp continuous_snd)))
  start := by
    rw [c.start]
    apply Homeomorph.ext
    intro x
    exact f.apply_symm_apply x
  finish := by rw [c.finish]

/-- An oriented chart transports images of sets under arbitrary coordinates. -/
theorem _root_.FiniteAvalanches.Electrical.Source.OrientedChart.conjugate_image
    (c : OrientedChart) (f : Plane ≃ₜ Plane)
    (K : Set Plane) :
    (c.conjugate f).map '' (f '' K) = f '' (c.map '' K) := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨c.map y, ⟨y, hy, rfl⟩, by simp [Source.OrientedChart.conjugate]⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨f y, ⟨y, hy, rfl⟩, ?_⟩
    simp [Source.OrientedChart.conjugate]

/-- A straightening locally agreeing with an oriented chart, possibly after
reflection of the target, has an oriented straightening. -/
theorem exists_orientedChart_straightening_of_local_agreement
    (gamma : unitInterval → Plane) (f : Plane ≃ₜ Plane)
    (hf : ∀ t, f (gamma t) = (t.val, 0)) (c : OrientedChart) (z : Plane)
    (hlocal : f =ᶠ[𝓝 z] c.map ∨
      f =ᶠ[𝓝 z] (planeReflection.symm ∘ c.map)) :
    ∃ d : OrientedChart, ∀ t, d.map (gamma t) = (t.val, 0) := by
  rcases hlocal with h | h
  · exact ⟨orientedChartOfLocallyEq f c z h, hf⟩
  · have h' : f.trans planeReflection =ᶠ[𝓝 z] c.map := by
      filter_upwards [h] with x hx
      change planeReflection (f x) = c.map x
      rw [hx]
      exact planeReflection.apply_symm_apply (c.map x)
    refine ⟨orientedChartOfLocallyEq (f.trans planeReflection) c z h', ?_⟩
    intro t
    change planeReflection (f (gamma t)) = (t.val, 0)
    rw [hf, planeReflection_horizontal]

end
end FiniteAvalanches.Electrical.StatementGeometry
