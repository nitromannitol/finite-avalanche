import FiniteAvalanches.Paper.Revision4498.ColorApplications

set_option autoImplicit false
namespace FiniteAvalanches.Paper.Revision4498
open LatticeProb MeasureTheory Filter FiniteAvalanches.Wilson.Lattice
open scoped Classical
noncomputable section

theorem color_cylinder_tendsto (Rj : ℕ → RootPair) (R : RootPair)
    (hzero : ∀ x, ∀ᶠ j in atTop, x ∈ (Rj j).zero ↔ x ∈ R.zero)
    (hone : ∀ x, ∀ᶠ j in atTop, x ∈ (Rj j).one ↔ x ∈ R.one)
    (F : Finset (Site 2)) (p : F → Bool) :
    Tendsto (fun j => wilsonColorLaw (Rj j) (colorCylinder F p)) atTop
      (nhds (wilsonColorLaw R (colorCylinder F p))) := by
  exact FiniteAvalanches.Paper.Revised.color_cylinder_tendsto Rj R hzero hone F p

end
end FiniteAvalanches.Paper.Revision4498
