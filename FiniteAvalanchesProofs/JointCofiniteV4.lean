import FiniteAvalanches.Wilson.Lattice.RevealedRoots.ReferenceConditional
import FiniteAvalanchesFrozen.ElectricalReferenceMomentV4
import FiniteAvalanches.Wilson.Lattice.Law
import FiniteAvalanches.Wilson.Lattice.ForestEvents

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option pp.all true
set_option pp.maxSteps 1000000

namespace FiniteAvalanchesProofs.JointCofiniteV4
open FiniteAvalanches.Wilson.Lattice
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory
open scoped Classical
noncomputable section

theorem local_comparison_and_revealed_roots_v4 :
    (∃ ε : ℝ, 0 < ε ∧
  (∀ (r : ℕ), 10 ^ 30 ≤ r → ∀ (R : RootPair),
    (R.zero ∪ R.one)ᶜ.Finite →
    0 ∈ R.zero →
    (∃ b ∈ R.one, (lattice 2).Adj 0 b) →
    ((lattice 2).induce R.zero).Connected →
    (∃ x ∈ R.zero, 2 * r ≤ siteRadius 0 x) →
    ((lattice 2).induce R.one).Connected →
    (∃ y ∈ R.one, siteRadius 0 y = r) →
    ε ≤ (wilsonColorLaw R).real
      (localContactEvent R.zero 0 (2 * r) ((1 / 8 : ℝ) * Real.log (r : ℝ)))) ∧
  (∃ κ : ℕ, 30 ≤ κ ∧
    ∀ (K : Finset (Site 2)) (γ : Set (Site 2)),
      ((lattice 2).induce (K : Set (Site 2))).Connected →
      0 ∈ K → Disjoint (K : Set (Site 2)) γ →
      ((lattice 2).induce γ).Connected → γᶜ.Finite →
      (∃ b ∈ γ, (lattice 2).Adj 0 b) →
      ∀ (h r : ℕ), 10 ≤ h → h ^ κ ≤ r →
      16 * r ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) →
      ∀ (R : RootPair), (K : Set (Site 2)) ⊆ R.zero →
        R.zero ⊆ (K : Set (Site 2)) ∪ (boxSites h : Set (Site 2)) →
        γ ⊆ R.one →
        ε / 2 ≤ (wilsonColorLaw R).real
          (kContactEvent K (3 * (r : ℝ)) ((1 / 16 : ℝ) * Real.log (r : ℝ))))) := by
  exact FiniteAvalanches.Wilson.Lattice.SourceTargets.local_comparison_and_revealed_roots_of_reference_v3
    FiniteAvalanches.Electrical.Source.Reference.reference_moment_v4

end
end FiniteAvalanchesProofs.JointCofiniteV4
