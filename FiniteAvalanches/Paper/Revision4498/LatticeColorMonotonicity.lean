import FiniteAvalanches.Paper.Revision4498.ColorApplications

set_option autoImplicit false
namespace FiniteAvalanches.Paper.Revision4498
open LatticeProb MeasureTheory Filter FiniteAvalanches.Wilson.Lattice
open scoped Classical
noncomputable section

theorem color_window_mono (R Q : RootPair)
    (hzero : R.zero ⊆ Q.zero) (hone : Q.one ⊆ R.one)
    (W : Finset (Site 2)) (H : Set (W → Bool))
    (hH : ∀ p ∈ H, ∀ q : W → Bool,
      (∀ x, p x = true → q x = true) → q ∈ H) :
    (wilsonColorLaw Q).real (windowColorEvent W H) ≤
      (wilsonColorLaw R).real (windowColorEvent W H) := by
  exact FiniteAvalanches.Paper.Revised.color_window_mono R Q hzero hone W H hH

end
end FiniteAvalanches.Paper.Revision4498
