import FiniteAvalanches.Wilson.Lattice.WiredConflictingColors

/-! Rooted-forest support supplies the remaining Wilson color condition. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- If selected edges preserve colors, every finite selected path preserves colors. -/
theorem color_eq_of_reachable (ω : ForestField)
    (hedge : ∀ x y (hxy : (lattice 2).Adj x y),
      ω.1 ⟨s(x, y), hxy⟩ = true → ω.2 x = ω.2 y)
    {x y : Site 2} (hxy : (toGraph ω.1).Reachable x y) : ω.2 x = ω.2 y := by
  have hp := ((toGraph ω.1).reachable_iff_reflTransGen x y).mp hxy
  clear hxy
  induction hp with
  | refl => rfl
  | @tail u v hpath hstep ih =>
    obtain ⟨h, he⟩ := hstep
    exact ih.trans (hedge u v h he)

/-- Correct root colors and edgewise color agreement identify the component
colors of any rooted forest. -/
theorem is_colored_forest_of_rooted_and_colors (R : RootPair) (ω : ForestField)
    (hf : is_rooted_forest R ω.1)
    (h0 : ∀ r ∈ R.zero, ω.2 r = false)
    (h1 : ∀ r ∈ R.one, ω.2 r = true)
    (hedge : ∀ x y (hxy : (lattice 2).Adj x y),
      ω.1 ⟨s(x, y), hxy⟩ = true → ω.2 x = ω.2 y) :
    is_colored_forest R ω := by
  refine ⟨hf, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨r, hr, hreach, _⟩ := hf.2 x
    rcases hr with hr | hr
    · have hc := color_eq_of_reachable ω hedge hreach
      rw [hx, h0 r hr] at hc
      cases hc
    · exact ⟨r, hr, hreach⟩
  · rintro ⟨r, hr, hreach⟩
    exact (color_eq_of_reachable ω hedge hreach).trans (h1 r hr)

/-- For the cylinder law, proving rooted-forest support automatically proves
all of the colored-forest support required by the Wilson law. -/
theorem IsWilsonCylinderLaw.ae_colored_of_ae_rooted (R : RootPair)
    (ν : ProbabilityMeasure ForestField) (hν : IsWilsonCylinderLaw R ν)
    (hf : ∀ᵐ ω ∂(ν : Measure ForestField), is_rooted_forest R ω.1) :
    ∀ᵐ ω ∂(ν : Measure ForestField), is_colored_forest R ω := by
  filter_upwards [hf, hν.ae_root_colors R ν, hν.ae_edge_colors R ν] with ω hf' hroots hedges
  exact is_colored_forest_of_rooted_and_colors R ω hf' hroots.1 hroots.2 hedges

/-- The complete Wilson law and its wired weak limit follow from rooted-forest
support of the cylinder law. -/
theorem wilsonLaw_existsUnique_of_cylinder_rooted_support (R : RootPair)
    (ν : ProbabilityMeasure ForestField) (hν : IsWilsonCylinderLaw R ν)
    (hf : ∀ᵐ ω ∂(ν : Measure ForestField), is_rooted_forest R ω.1) :
    (∃! μ : ProbabilityMeasure ForestField, IsWilsonLaw R μ) ∧
    ∀ μ : ProbabilityMeasure ForestField, IsWilsonLaw R μ →
      Filter.Tendsto (finiteForestProbability R) Filter.atTop (nhds μ) :=
  wilsonLaw_existsUnique_of_cylinder_support R ν hν (hν.ae_colored_of_ae_rooted R ν hf)

end
end FiniteAvalanches.Wilson.Lattice
