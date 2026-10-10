import FiniteAvalanches.Paper.Providers.ColorLawContinuityProvider
import FiniteAvalanches.Wilson.Lattice.Law
import FiniteAvalanches.Wilson.Lattice.ForestEvents
import FiniteAvalanches.Wilson.Lattice.ContinuityRoots

set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.SourceTargets
open LatticeProb FiniteAvalanches.Trees.Lattice FiniteAvalanches.Sandpile MeasureTheory Filter
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
  exact FiniteAvalanchesProofs.ColorLawContinuity.color_law_continuity

end
end FiniteAvalanches.Wilson.Lattice.SourceTargets
