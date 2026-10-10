import FiniteAvalanches.Paper.RevisionB972.WiredRootContinuity

set_option autoImplicit false
namespace FiniteAvalanches.Paper.RevisionB972
open LatticeProb MeasureTheory Filter FiniteAvalanches.Wilson.Lattice
open scoped Classical
noncomputable section

/-- The literal wired color law converges on its actual nonempty-root volumes. -/
theorem wired_color_continuity_v4 (R : RootPair)
    (F : Finset (Site 2)) (p : F → Bool) :
    Tendsto
      (fun N : {N : ℕ // (wiredZeroSites R N).Nonempty} =>
        wilsonColorLaw (wiredRootPair R N.val N.property) (colorCylinder F p))
      (Filter.comap Subtype.val atTop)
      (nhds (wilsonColorLaw R (colorCylinder F p))) := by
  have h := (wired_color_cylinder_tendsto R F p).comp
    (Filter.tendsto_comap : Tendsto
      (Subtype.val : {N : ℕ // (wiredZeroSites R N).Nonempty} → ℕ)
      (Filter.comap Subtype.val atTop) atTop)
  apply h.congr'
  exact Filter.Eventually.of_forall fun N => by
    simp only [Function.comp_apply, wiredPrefixCompletion, dif_pos N.property]

end
end FiniteAvalanches.Paper.RevisionB972
