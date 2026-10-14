import FiniteAvalanches.Wilson.Lattice.ConsecutivePrefixContraction

/-! Countable complete-history atoms give the incoming conditional contraction on one full-measure set. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.CurrentGlobalContraction

open LatticeProb FiniteAvalanches Sandpile MeasureTheory Filter
open Probability.CurrentScale CurrentNestedPrefix CurrentObservedInverse ConditionalIteration7
open scoped Classical
noncomputable section

/-- The incoming conditional inverse-mean contraction holds almost surely on
confinement, without a completed-output, conditional-law or success premise. -/
theorem global_prefix_inverse_contraction :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∃ κ : ℕ, 30 ≤ κ ∧ 73728 ≤ ε*(κ : ℝ) ∧
      ∀ (K : Finset (Site 2)) (γ : Set (Site 2)),
      ((lattice 2).induce (K : Set (Site 2))).Connected →
      (0 : Site 2) ∈ K → Disjoint (K : Set (Site 2)) γ →
      ((lattice 2).induce γ).Connected → γᶜ.Finite →
      (∃ y ∈ γ, (lattice 2).Adj 0 y) →
      ∀ R : RootPair, R.zero = (K : Set (Site 2)) → R.one = γ →
      ∀ i : ℕ, 1 ≤ i →
      16 * scale (6 * κ) (i + 1) ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) →
      ∀ᵐ ξ ∂wilsonRows,
        ξ ∉ ActualLocalizationUnion.prefixExit R (stagePrefix (6 * κ) i)
          (scale (6 * κ) i ^ 6) →
        (wilsonRows[observedInverseContacts R (stagePrefix (6 * κ) (i + 1))
          (sourceWindow K (6 * κ) (i + 1)) | fullHistory R (stagePrefix (6 * κ) i)]) ξ ≤
        (1 - ε / 2) * observedInverseContacts R (stagePrefix (6 * κ) i)
          (sourceWindow K (6 * κ) i) ξ + 16 / Real.log (scale (6 * κ) (i + 1) : ℝ) := by
  obtain ⟨ε, hε, hεsmall, κ, hκ, hpaid, hbound⟩ :=
    CurrentConsecutiveContraction.consecutive_prefix_inverse_contraction
  refine ⟨ε, hε, hεsmall, κ, hκ, hpaid, ?_⟩
  intro K γ hK h0 hd hγ hγfin hγadj R hz ho i hi hdiam
  let L := stagePrefix (6 * κ) i
  let h := scale (6 * κ) i ^ 6
  let A : Set SamplerState := {out | ∃ ξ₀ : Rows,
    samplerRun (initialSampler R) L ξ₀ = some out ∧
      ξ₀ ∉ ActualLocalizationUnion.prefixExit R L h}
  have hA : A.Countable := (reachable_states_countable R L).mono (by
    intro out hout
    obtain ⟨ξ₀, hs, _hgood⟩ := hout
    exact ⟨ξ₀, hs⟩)
  have hatoms : ∀ᵐ ξ ∂wilsonRows, ∀ out ∈ A, ξ ∈ historyAtom R L out →
      (wilsonRows[observedInverseContacts R (stagePrefix (6 * κ) (i + 1))
        (sourceWindow K (6 * κ) (i + 1)) | fullHistory R L]) ξ ≤
      (1 - ε / 2) * observedInverseContacts R L (sourceWindow K (6 * κ) i) ξ +
        16 / Real.log (scale (6 * κ) (i + 1) : ℝ) := by
    apply (ae_ball_iff hA).mpr
    intro out hout
    obtain ⟨ξ₀, hs, hgood⟩ := hout
    exact hbound K γ hK h0 hd hγ hγfin hγadj R hz ho i hi hdiam ξ₀ out hs hgood
  filter_upwards [hatoms, wilson_sampler_success_conull R L] with ξ hξ hs hgood
  obtain ⟨out, hs⟩ := hs
  exact hξ out ⟨ξ, hs, hgood⟩ hs

end
end FiniteAvalanches.Wilson.Lattice.CurrentGlobalContraction
