import FiniteAvalanches.Wilson.Lattice.CompletedPrefixContraction
import FiniteAvalanches.Wilson.Lattice.ObservedInverseContact
import FiniteAvalanches.Wilson.Lattice.CurrentPrefixLocalization

/-! The incoming conditional inverse-contact contraction at consecutive source scales. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.CurrentConsecutiveContraction

open LatticeProb FiniteAvalanches Sandpile MeasureTheory Filter
open Probability.CurrentScale CurrentNestedPrefix CurrentPrefixLocalization
open CurrentInverseContact CurrentObservedInverse CurrentCompletedContraction BatchRestart ConditionalIteration7
open scoped Classical
noncomputable section

/-- The actual next source window is observed after exactly the newly requested sites. -/
theorem next_contacts_known_or_requested (R : RootPair) (K : Finset (Site 2))
    (b : ℕ) (hb : 6 ≤ b) (i : ℕ) (ξ₀ : Rows) (out : SamplerState)
    (hs : samplerRun (initialSampler R) (stagePrefix b i) ξ₀ = some out) :
    ∀ d ∈ contactSites (sourceWindow K b (i + 1)), d ∈ out.covered ∨
      d ∈ (stageBox b (i + 1) \ (stagePrefix b i).toFinset).toList := by
  intro d hd
  have hqueried := source_and_contact_queried K b hb (i + 1) (by omega) d
    (Finset.mem_union_right _ hd)
  rw [CurrentNestedPrefix.prefix_succ] at hqueried
  rcases List.mem_append.mp hqueried with h | h
  · exact Or.inl (samplerRun_covers_queries _ out _ ξ₀ hs d h)
  · exact Or.inr h

/-- The contraction uses the same filtration and the actual earlier observed
inverse; all scale, coverage, positivity and root hypotheses are supplied internally. -/
theorem consecutive_prefix_inverse_contraction :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∃ κ : ℕ, 30 ≤ κ ∧ 73728 ≤ ε*(κ : ℝ) ∧
      ∀ (K : Finset (Site 2)) (γ : Set (Site 2)),
      ((lattice 2).induce (K : Set (Site 2))).Connected →
      (0 : Site 2) ∈ K → Disjoint (K : Set (Site 2)) γ →
      ((lattice 2).induce γ).Connected → γᶜ.Finite →
      (∃ y ∈ γ, (lattice 2).Adj 0 y) →
      ∀ R : RootPair, R.zero = (K : Set (Site 2)) → R.one = γ →
      ∀ i : ℕ, 1 ≤ i →
      16 * scale (6 * κ) (i + 1) ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) →
      ∀ (ξ₀ : Rows) (out : SamplerState)
      (_hs : samplerRun (initialSampler R) (stagePrefix (6 * κ) i) ξ₀ = some out),
      ξ₀ ∉ ActualLocalizationUnion.prefixExit R (stagePrefix (6 * κ) i)
        (scale (6 * κ) i ^ 6) →
      ∀ᵐ ξ ∂wilsonRows, ξ ∈ historyAtom R (stagePrefix (6 * κ) i) out →
        (wilsonRows[observedInverseContacts R (stagePrefix (6 * κ) (i + 1))
          (sourceWindow K (6 * κ) (i + 1)) | fullHistory R (stagePrefix (6 * κ) i)]) ξ ≤
        (1 - ε / 2) * observedInverseContacts R (stagePrefix (6 * κ) i)
          (sourceWindow K (6 * κ) i) ξ + 16 / Real.log (scale (6 * κ) (i + 1) : ℝ) := by
  obtain ⟨ε, hε, hεsmall, κ, hκ, hpaid, hcontract⟩ := completed_prefix_inverse_contraction
  refine ⟨ε, hε, hεsmall, κ, hκ, hpaid, ?_⟩
  intro K γ hK h0 hd hγ hγfin hγadj R hz ho i hi hdiam ξ₀ out hs hgood
  let b := 6 * κ
  have hb : 6 ≤ b := by dsimp only [b]; omega
  let L := stagePrefix b i
  let Q := (stageBox b (i + 1) \ (stagePrefix b i).toFinset).toList
  let F := sourceWindow K b i
  let H := sourceWindow K b (i + 1)
  have hh : 10 ≤ scale b i ^ 6 := by
    have h2 := two_le_scale b hb i
    have hh64 : 64 ≤ scale b i ^ 6 := by exact_mod_cast Nat.pow_le_pow_left h2 6
    omega
  have hr : (scale b i ^ 6) ^ κ ≤ scale b (i + 1) := by
    rw [scale_succ_eq_pow, ← pow_mul]
  have hF0 : (0 : Site 2) ∈ F := by
    apply Finset.mem_filter.mpr
    refine ⟨h0, ?_⟩
    apply Finset.sup_le
    intro j _hj
    simp only [Pi.zero_apply, sub_self, Int.natAbs_zero]
    exact Nat.zero_le _
  have hFH : F ⊆ K.filter (fun x => (siteRadius 0 x : ℝ) ≤ 3 * (scale b (i + 1) : ℝ)) := by
    rw [← sourceWindow_eq_real_filter]
    intro x hx
    obtain ⟨hxK, hxrad⟩ := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr
    exact ⟨hxK, hxrad.trans (Nat.mul_le_mul_left 3 (scale_mono b hb (Nat.le_succ i)))⟩
  have hknown := completed_prefix_contact_known R K b hb i hi ξ₀ out hs
  choose p hp using (fun d : contactSites F => hknown d.val (Finset.mem_union_right _ d.property))
  have hD := next_contacts_known_or_requested R K b hb i ξ₀ out hs
  have hm := hcontract K γ hK h0 hd hγ hγfin hγadj (scale b i ^ 6) (scale b (i + 1))
    hh hr hdiam R hz ho L Q ξ₀ out hs hgood F p hF0 hFH hp
    (by simpa only [← sourceWindow_eq_real_filter] using hD)
  have hcond := conditional_observedInverseContacts R L Q ξ₀ out hs H hD
  have hsum := conditional_inverse_contacts_known R L Q ξ₀ out hs H hD
  filter_upwards [hm, hcond, hsum] with ξ hm' hc' hsum' hhist
  have hpξ : ξ ∈ observedPattern (initialSampler R) L F p := ⟨out, hhist, hp⟩
  have hzξ := observedInverseContacts_of_pattern R L F p ξ hpξ
  have hmass : (wilsonRows[observedInverseContacts R (stagePrefix b (i + 1)) H |
      fullHistory R L]) ξ =
      ∫ σ, (contacts H σ : ℝ)⁻¹ ∂wilsonColorLaw (restartedRoots R L ξ₀ out hs) := by
    rw [CurrentNestedPrefix.prefix_succ]
    exact hc' hhist
  rw [hmass, hzξ]
  have hbound := hm' hhist
  rw [← sourceWindow_eq_real_filter] at hbound
  rw [hsum' hhist] at hbound
  exact hbound

end
end FiniteAvalanches.Wilson.Lattice.CurrentConsecutiveContraction
