import FiniteAvalanches.Wilson.Lattice.TranslationColorLaw
import FiniteAvalanches.Wilson.Lattice.TranslationGeometry
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Transport of the complete contact distribution and its real expectation
under the exact Wilson color-law pushforward identity. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.Translation
open LatticeProb MeasureTheory
open scoped Classical
noncomputable section

/-- Every measurable contact event has its exact probability after translation. -/
theorem contact_distribution_translate (R : RootPair) (K : Finset (Site 2))
    (z : Site 2) :
    (wilsonColorLaw (roots R z)).map (contacts (finiteSet K z)) =
      (wilsonColorLaw R).map (contacts K) := by
  rw [← wilsonColorLaw_map, Measure.map_map (continuous_contacts _).measurable
    (measurable_colors z)]
  congr 1
  funext σ
  exact contacts_translate K z σ

/-- The entire original-copy contact count is retained in any real function of
contacts; neither a truncated event nor a forest-edge contact count is substituted. -/
theorem contact_expectation_translate (R : RootPair) (K : Finset (Site 2))
    (z : Site 2) (f : ℕ → ℝ) :
    (∫ σ, f (contacts (finiteSet K z) σ) ∂wilsonColorLaw (roots R z)) =
      ∫ σ, f (contacts K σ) ∂wilsonColorLaw R := by
  rw [← wilsonColorLaw_map]
  have hf : StronglyMeasurable (fun σ : ColorField => f (contacts (finiteSet K z) σ)) :=
    ((measurable_of_countable f).comp (continuous_contacts _).measurable).stronglyMeasurable
  rw [integral_map_of_stronglyMeasurable (measurable_colors z) hf]
  simp only [contacts_translate]

theorem reciprocal_expectation_translate (R : RootPair) (K : Finset (Site 2))
    (z : Site 2) :
    (∫ σ, (1 : ℝ) / (contacts (finiteSet K z) σ : ℝ) ∂wilsonColorLaw (roots R z)) =
      ∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw R :=
  contact_expectation_translate R K z (fun n => (1 : ℝ) / (n : ℝ))

/-- The source's literal zero roots are every translated finite-set site. -/
theorem roots_zero (R : RootPair) (K : Finset (Site 2)) (z : Site 2)
    (h : R.zero = (K : Set (Site 2))) :
    (roots R z).zero = (finiteSet K z : Set (Site 2)) := by
  ext x
  exact (by change x - z ∈ R.zero ↔ x ∈ finiteSet K z; rw [h]; exact (mem_finiteSet K z x).symm)

/-- The source's literal one roots are the entire translated infinite ray. -/
theorem roots_one (R : RootPair) (γ : SimpleRay) (z : Site 2)
    (h : R.one = γ.vertices) : (roots R z).one = (ray γ z).vertices := by
  rw [ray_vertices]
  change {x | x - z ∈ R.one} = {x | x - z ∈ γ.vertices}
  rw [h]

end
end FiniteAvalanches.Wilson.Lattice.Translation
