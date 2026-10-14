import FiniteAvalanches.Wilson.Lattice.LocalComparison.CurrentLocal
import FiniteAvalanches.Wilson.Lattice.CurrentSource.RevealedProbability

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.CurrentForestJoint
open LatticeProb FiniteAvalanches Sandpile MeasureTheory
open scoped Classical
noncomputable section

/-- The produced local proof supplies epsilon before the current paid kappa. -/
theorem local_and_revealed :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      (∀ (r : ℕ), 10 ^ 30 ≤ r → ∀ R : RootPair,
        (R.zero ∪ R.one)ᶜ.Finite → 0 ∈ R.zero →
        (∃ b ∈ R.one, (lattice 2).Adj 0 b) →
        ((lattice 2).induce R.zero).Connected →
        (∃ x ∈ R.zero, 2 * r ≤ siteRadius 0 x) →
        ((lattice 2).induce R.one).Connected →
        (∃ y ∈ R.one, siteRadius 0 y = r) →
        ε ≤ (wilsonColorLaw R).real
          (localContactEvent R.zero 0 (2 * r) ((1 / 8 : ℝ) * Real.log (r : ℝ)))) ∧
      ∃ κ : ℕ, 30 ≤ κ ∧ 73728 ≤ ε * (κ : ℝ) ∧
        ∀ (K : Finset (Site 2)) (γ : Set (Site 2)),
          ((lattice 2).induce (K : Set (Site 2))).Connected →
          0 ∈ K → Disjoint (K : Set (Site 2)) γ →
          ((lattice 2).induce γ).Connected → γᶜ.Finite →
          (∃ b ∈ γ, (lattice 2).Adj 0 b) →
          ∀ h r : ℕ, 10 ≤ h → h ^ κ ≤ r →
          16 * r ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) →
          ∀ R : RootPair, (K : Set (Site 2)) ⊆ R.zero →
            R.zero ⊆ (K : Set (Site 2)) ∪ (boxSites h : Set (Site 2)) →
            γ ⊆ R.one →
            ε / 2 ≤ (wilsonColorLaw R).real
              (kContactEvent K (3 * (r : ℝ)) ((1 / 16 : ℝ) * Real.log (r : ℝ))) := by
  obtain ⟨ε₀, hε₀, hlocal₀⟩ := CurrentLocalComparison.current_local_comparison
  let ε : ℝ := min ε₀ (1 / 2)
  have hε : 0 < ε := lt_min hε₀ (by norm_num)
  have hεsmall : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hlocal : ∀ (r : ℕ), 10 ^ 30 ≤ r → ∀ R : RootPair,
      (R.zero ∪ R.one)ᶜ.Finite → 0 ∈ R.zero →
      (∃ b ∈ R.one, (lattice 2).Adj 0 b) →
      ((lattice 2).induce R.zero).Connected →
      (∃ x ∈ R.zero, 2 * r ≤ siteRadius 0 x) →
      ((lattice 2).induce R.one).Connected →
      (∃ y ∈ R.one, siteRadius 0 y = r) →
      ε ≤ (wilsonColorLaw R).real
        (localContactEvent R.zero 0 (2 * r) (Real.log (r : ℝ) / 8)) := by
    intro r hr R hcf h0 hn hzc hfar hoc hmeet
    exact (min_le_left _ _).trans (hlocal₀ r hr R hcf h0 hn hzc hfar hoc hmeet)
  obtain ⟨κ, hκ, hpaid, hrevealed⟩ :=
    CurrentRevealedProbability.revealed_of_local ε hε hlocal
  refine ⟨ε, hε, hεsmall, ?_, κ, hκ, hpaid, ?_⟩
  · intro r hr R hcf h0 hn hzc hfar hoc hmeet
    rw [show (1 / 8 : ℝ) * Real.log (r : ℝ) = Real.log (r : ℝ) / 8 by ring]
    exact hlocal r hr R hcf h0 hn hzc hfar hoc hmeet
  · intro K γ hK h0 hd hγc hγf hn h r hh hr hdiam R hRK hRbox hRγ
    rw [show (1 / 16 : ℝ) * Real.log (r : ℝ) = Real.log (r : ℝ) / 16 by ring]
    exact hrevealed K γ hK h0 hd hγc hγf hn h r hh hr hdiam R hRK hRbox hRγ

end
end FiniteAvalanches.Wilson.Lattice.CurrentForestJoint
