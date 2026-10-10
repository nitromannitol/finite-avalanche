import FiniteAvalanches.Probability.LogDiameterComparison
import FiniteAvalanches.Wilson.Lattice.PrependRay
import FiniteAvalanches.Wilson.Lattice.ReciprocalContactMonotonicity

/-! An ordinary conditional application of the closed forest estimate. -/

namespace FiniteAvalanches.Wilson.Lattice.ConditionalInternal

open LatticeProb FiniteAvalanches.Sandpile MeasureTheory
open scoped Classical
noncomputable section

/-- A closed uniform forest estimate supplies common positive constants for
larger one-root sets and smaller diameter scales. This is an internal
conditional implication; it supplies no observation or escaping-ray geometry. -/
theorem uniform_enlarged_roots_bound_of_closed_forest_bound
    (hforest : ∃ a C : ℝ, 0 < a ∧ ∀ K : Finset (Site 2),
      ((lattice 2).induce (K : Set (Site 2))).Connected →
      ∀ γ : SimpleRay, Disjoint (K : Set (Site 2)) γ.vertices →
        (∃ k ∈ K, (lattice 2).Adj k (γ.vertex 0)) →
        ∀ R : RootPair, R.zero = (K : Set (Site 2)) → R.one = γ.vertices →
          (∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw R) ≤
            C * Real.rpow
              (Real.log (((K.sup (fun x => K.sup (fun y => siteRadius x y)) : ℕ) : ℝ) + 2))
              (-a)) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ r : ℕ, ∀ K : Finset (Site 2),
      ((lattice 2).induce (K : Set (Site 2))).Connected →
      r ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) →
      ∀ γ : SimpleRay, Disjoint (K : Set (Site 2)) γ.vertices →
        (∃ k ∈ K, (lattice 2).Adj k (γ.vertex 0)) →
        ∀ R : RootPair, R.zero = (K : Set (Site 2)) → γ.vertices ⊆ R.one →
          (∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw R) ≤
            C * Real.rpow (Real.log ((r : ℝ) + 2)) (-a) := by
  obtain ⟨a, C, ha, hbound⟩ := hforest
  refine ⟨a, max C 1, ha, zero_lt_one.trans_le (le_max_right C 1), ?_⟩
  intro r K hK hdiam γ hdisj hadj R hR hsub
  obtain ⟨k, hk, hkγ⟩ := hadj
  have hfree : ∀ n, γ.vertex n ∉ K := by
    intro n hn
    exact Set.disjoint_left.mp hdisj hn ⟨n, rfl⟩
  let Q := (prependConnectingPair K hK γ k hk hkγ hfree).roots
  have hQzero : Q.zero = (K : Set (Site 2)) :=
    (prependConnectingPair_roots K hK γ k hk hkγ hfree).1
  have hQone : Q.one = γ.vertices :=
    (prependConnectingPair_roots K hK γ k hk hkγ hfree).2
  have hQsub : Q.one ⊆ R.one := by
    rw [hQone]
    exact hsub
  have hγ0 : γ.vertex 0 ∈ Q.one := by
    rw [hQone]
    exact ⟨0, rfl⟩
  calc
    _ ≤ ∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw Q :=
      integral_reciprocal_contacts_one_roots_mono Q R K hQzero hR hQsub
        k (γ.vertex 0) hk hγ0 hkγ
    _ ≤ C * Real.rpow
        (Real.log (((K.sup (fun x => K.sup (fun y => siteRadius x y)) : ℕ) : ℝ) + 2))
        (-a) := hbound K hK γ hdisj ⟨k, hk, hkγ⟩ Q hQzero hQone
    _ ≤ _ := FiniteAvalanches.mul_log_rpow_neg_le_max_of_nat_le a C ha.le hdiam

end
end FiniteAvalanches.Wilson.Lattice.ConditionalInternal
