import FiniteAvalanches.Wilson.Lattice.ColorContinuity
import FiniteAvalanches.Wilson.Lattice.ColorMonotonicity

/-! Finite color-law applications for locally converging and ordered root sets. -/

set_option autoImplicit false
namespace FiniteAvalanches.Paper.Revised
open LatticeProb MeasureTheory Filter FiniteAvalanches.Wilson.Lattice
open scoped Classical
noncomputable section

/-- Local agreement of the two root sets suffices; common roots for all
indices are not needed. -/
theorem color_cylinder_tendsto (Rj : ℕ → RootPair) (R : RootPair)
    (hzero : ∀ x, ∀ᶠ j in atTop, x ∈ (Rj j).zero ↔ x ∈ R.zero)
    (hone : ∀ x, ∀ᶠ j in atTop, x ∈ (Rj j).one ↔ x ∈ R.one)
    (F : Finset (Site 2)) (p : F → Bool) :
    Tendsto (fun j => wilsonColorLaw (Rj j) (colorCylinder F p)) atTop
      (nhds (wilsonColorLaw R (colorCylinder F p))) := by
  apply colorCylinder_tendsto_of_local_roots
  intro x
  filter_upwards [hzero x, hone x] with j h0 h1
  exact ⟨h0, h1⟩

/-- Adding zero roots and removing one roots simultaneously decreases every
increasing event of the joint color pattern in a finite window. -/
theorem color_window_mono (R Q : RootPair)
    (hzero : R.zero ⊆ Q.zero) (hone : Q.one ⊆ R.one)
    (W : Finset (Site 2)) (H : Set (W → Bool))
    (hH : ∀ p ∈ H, ∀ q : W → Bool,
      (∀ x, p x = true → q x = true) → q ∈ H) :
    (wilsonColorLaw Q).real (windowColorEvent W H) ≤
      (wilsonColorLaw R).real (windowColorEvent W H) := by
  let M : RootPair :=
    { zero := R.zero
      one := Q.one
      disjoint := R.disjoint.mono_right hone
      zero_nonempty := R.zero_nonempty
      one_nonempty := Q.one_nonempty }
  have hQM : (wilsonColorLaw Q).real (windowColorEvent W H) ≤
      (wilsonColorLaw M).real (windowColorEvent W H) :=
    color_window_zero_roots_added M Q hzero rfl W H hH
  have hMR : (wilsonColorLaw M).real (windowColorEvent W H) ≤
      (wilsonColorLaw R).real (windowColorEvent W H) :=
    color_window_one_roots_removed R M rfl hone W H hH
  exact hQM.trans hMR

end
end FiniteAvalanches.Paper.Revised
