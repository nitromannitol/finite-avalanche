import FiniteAvalanches.Wilson.Lattice.PrependRay
import FiniteAvalanches.Wilson.Lattice.Law
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Conditional transport of a uniform contact bound to a whole disjoint ray. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.ConditionalInternal
open LatticeProb FiniteAvalanches.Sandpile MeasureTheory
open scoped Classical
noncomputable section

private theorem rootPair_eq_of_sets_eq (R S : RootPair)
    (hzero : R.zero = S.zero) (hone : R.one = S.one) : R = S := by
  cases R
  cases S
  cases hzero
  cases hone
  rfl

/-- A closed uniform bound on connecting pairs implies the whole disjoint-ray
formulation, using the same witnesses for the universal constants. -/
theorem whole_disjoint_ray_bound_of_connecting_pair_bound :
    (∃ a C : ℝ, 0 < a ∧ ∀ p : ConnectingPair,
      (∫ σ, (1 : ℝ) / (contacts p.sites σ : ℝ) ∂wilsonColorLaw p.roots) ≤
        C * Real.rpow
          (Real.log (((p.sites.sup (fun x => p.sites.sup (fun y => siteRadius x y)) : ℕ) : ℝ) + 2))
          (-a)) →
    ∃ a C : ℝ, 0 < a ∧ ∀ K : Finset (Site 2),
      ((lattice 2).induce (K : Set (Site 2))).Connected →
      ∀ γ : SimpleRay, Disjoint (K : Set (Site 2)) γ.vertices →
        (∃ k ∈ K, (lattice 2).Adj k (γ.vertex 0)) →
        ∀ R : RootPair, R.zero = (K : Set (Site 2)) → R.one = γ.vertices →
          (∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw R) ≤
            C * Real.rpow
              (Real.log (((K.sup (fun x => K.sup (fun y => siteRadius x y)) : ℕ) : ℝ) + 2))
              (-a) := by
  rintro ⟨a, C, ha, hbound⟩
  refine ⟨a, C, ha, ?_⟩
  intro K hK γ hdisjoint hadjacent R hzero hone
  obtain ⟨k, hk, hadj⟩ := hadjacent
  have hfree : ∀ n, γ.vertex n ∉ K := by
    intro n hn
    exact Set.disjoint_left.mp hdisjoint hn ⟨n, rfl⟩
  let p := prependConnectingPair K hK γ k hk hadj hfree
  have hroots := prependConnectingPair_roots K hK γ k hk hadj hfree
  have hpR : p.roots = R :=
    rootPair_eq_of_sets_eq p.roots R (hroots.1.trans hzero.symm)
      (hroots.2.trans hone.symm)
  have h := hbound p
  change (∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw p.roots) ≤
    C * Real.rpow
      (Real.log (((K.sup (fun x => K.sup (fun y => siteRadius x y)) : ℕ) : ℝ) + 2))
      (-a) at h
  rw [hpR] at h
  exact h

end
end FiniteAvalanches.Wilson.Lattice.ConditionalInternal
