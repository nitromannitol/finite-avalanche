import FiniteAvalanches.Wilson.Lattice.ColorContinuity

/-! Continuity of every finite color law for locally convergent original roots. -/
set_option autoImplicit false
namespace FiniteAvalanchesProofs.ColorLawContinuity
open LatticeProb FiniteAvalanches.Wilson.Lattice
open MeasureTheory Filter
open scoped Classical
noncomputable section

theorem color_law_continuity :
(∀ (Rj : ℕ → RootPair) (A C : Set (Site 2)) (hAC : Disjoint A C)
  (a b : Site 2) (ha : ∀ j, a ∈ (Rj j).zero) (hb : ∀ j, b ∈ (Rj j).one)
  (hA : ∀ x, ∀ᶠ j in atTop, x ∈ (Rj j).zero ↔ x ∈ A)
  (hC : ∀ x, ∀ᶠ j in atTop, x ∈ (Rj j).one ↔ x ∈ C),
  ∀ (F : Finset (Site 2)) (p : F → Bool),
    Tendsto (fun j => wilsonColorLaw (Rj j) (colorCylinder F p)) atTop
      (nhds (wilsonColorLaw (ContinuityAudit.limitRoots Rj A C hAC a b ha hb hA hC)
        (colorCylinder F p)))) := by
  exact colorCylinder_tendsto_of_fixed_roots

end
end FiniteAvalanchesProofs.ColorLawContinuity
