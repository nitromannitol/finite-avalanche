import FiniteAvalanches.Wilson.Lattice.CurrentForestJoint
import FiniteAvalanches.Wilson.Lattice.InverseContactContraction

/-! The revealed-root estimate contracts the inverse moment on the same completed history atom. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.CurrentCompletedContraction

open LatticeProb FiniteAvalanches Sandpile MeasureTheory Filter
open CurrentInverseContact CurrentInverseContraction CurrentNestedPrefix BatchRestart ConditionalIteration7
open scoped Classical
noncomputable section

/-- An original adjacent one-root makes the recorded finite contact pattern positive. -/
theorem recorded_pattern_pos (R : RootPair) (L : List (Site 2)) (ξ₀ : Rows)
    (out : SamplerState) (hs : samplerRun (initialSampler R) L ξ₀ = some out)
    (F : Finset (Site 2)) (p : contactSites F → Bool)
    (hp : ∀ d : contactSites F, out.colors d.val = some (p d))
    (k y : Site 2) (hk : k ∈ F) (hy : y ∈ R.one) (hky : (lattice 2).Adj k y) :
    0 < patternContacts F p := by
  have hroot := ActualRestartGeometry.original_roots_subset_restarted R L ξ₀ out hs
  have hpos := contacts_ge_one_ae_of_adjacent_one_root
    (restartedRoots R L ξ₀ out hs) F k y hk (hroot.2 hy) hky
  obtain ⟨σ, hσ, hc⟩ := (restarted_pattern_ae R L ξ₀ out hs F p hp).and hpos |>.exists
  have he := patternContacts_eq_contacts F p σ hσ
  omega

/-- Every genuine completed, confined prefix has the incoming inverse-mean
contraction on its own history atom, with one shared revealed-root witness. -/
theorem completed_prefix_inverse_contraction :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∃ κ : ℕ, 30 ≤ κ ∧ 73728 ≤ ε*(κ : ℝ) ∧
      ∀ (K : Finset (Site 2)) (γ : Set (Site 2)),
      ((lattice 2).induce (K : Set (Site 2))).Connected →
      (0 : Site 2) ∈ K → Disjoint (K : Set (Site 2)) γ →
      ((lattice 2).induce γ).Connected → γᶜ.Finite →
      (∃ y ∈ γ, (lattice 2).Adj 0 y) →
      ∀ (h r : ℕ), 10 ≤ h → h ^ κ ≤ r →
      16 * r ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) →
      ∀ R : RootPair, R.zero = (K : Set (Site 2)) → R.one = γ →
      ∀ (L Q : List (Site 2)) (ξ₀ : Rows) (out : SamplerState)
      (_hs : samplerRun (initialSampler R) L ξ₀ = some out),
      ξ₀ ∉ ActualLocalizationUnion.prefixExit R L h →
      ∀ (F : Finset (Site 2)) (p : contactSites F → Bool),
      (0 : Site 2) ∈ F → F ⊆ K.filter (fun x => (siteRadius 0 x : ℝ) ≤ 3 * (r : ℝ)) →
      (∀ d : contactSites F, out.colors d.val = some (p d)) →
      (∀ d ∈ contactSites (K.filter (fun x => (siteRadius 0 x : ℝ) ≤ 3 * (r : ℝ))),
        d ∈ out.covered ∨ d ∈ Q) →
      ∀ᵐ ξ ∂wilsonRows, ξ ∈ historyAtom R L out →
        (∑ q : contactSites (K.filter (fun x => (siteRadius 0 x : ℝ) ≤ 3 * (r : ℝ))) → Bool,
          (patternContacts (K.filter (fun x => (siteRadius 0 x : ℝ) ≤ 3 * (r : ℝ))) q : ℝ)⁻¹ *
            (wilsonRows[(observedPattern (initialSampler R) (L ++ Q)
              (K.filter (fun x => (siteRadius 0 x : ℝ) ≤ 3 * (r : ℝ))) q).indicator
              (fun _ => (1 : ℝ)) | fullHistory R L]) ξ) ≤
          (1 - ε / 2) * (patternContacts F p : ℝ)⁻¹ + 16 / Real.log (r : ℝ) := by
  obtain ⟨ε, hε, hεsmall, _hlocal, κ, hκ, hpaid, hrevealed⟩ :=
    CurrentForestJoint.local_and_revealed
  refine ⟨ε, hε, hεsmall, κ, hκ, hpaid, ?_⟩
  intro K γ hK h0 hd hγ hγfin hγadj h r hh hr hdiam R hz ho L Q ξ₀ out hs hgood
    F p hF0 hFH hp hD
  let R' := restartedRoots R L ξ₀ out hs
  let H := K.filter (fun x => (siteRadius 0 x : ℝ) ≤ 3 * (r : ℝ))
  have hroots := CurrentConfinedRestart.restarted_roots_of_not_prefixExit R L ξ₀ out hs h hgood
  have hKR : (K : Set (Site 2)) ⊆ R'.zero := by
    rw [← hz]
    exact hroots.1
  have hRbox : R'.zero ⊆ (K : Set (Site 2)) ∪ (boxSites h : Set (Site 2)) := by
    intro v hv
    rcases hroots.2.1 hv with hv | hv
    · exact Or.inl (hz ▸ hv)
    · exact Or.inr ((site_radius_zero_le_iff v h).mp hv)
  have hγR : γ ⊆ R'.one := by
    rw [← ho]
    exact hroots.2.2
  have htail : ε / 2 ≤ (wilsonColorLaw R').real
      (contactEvent H ((1 / 16 : ℝ) * Real.log (r : ℝ))) :=
    hrevealed K γ hK h0 hd hγ hγfin hγadj h r hh hr hdiam R' hKR hRbox hγR
  obtain ⟨y, hy, hay⟩ := hγadj
  have hp0 : 0 < patternContacts F p :=
    recorded_pattern_pos R L ξ₀ out hs F p hp 0 y hF0 (ho.symm ▸ hy) hay
  have hr1 : 1 < r := by
    have hk0 : κ ≠ 0 := by omega
    have hpow : h ≤ h ^ κ := Nat.le_self_pow hk0 h
    omega
  have hlog : 0 < Real.log (r : ℝ) := Real.log_pos (by exact_mod_cast hr1)
  have hm := inverse_contacts_integral_le R' H (patternContacts F p : ℝ)⁻¹
    ((1 / 16 : ℝ) * Real.log (r : ℝ)) (ε / 2) (inv_nonneg.mpr (Nat.cast_nonneg _))
    (mul_pos (by norm_num) hlog)
    (by simpa only [one_div] using restarted_inverse_cap R L ξ₀ out hs F H p hp hFH hp0)
    htail
  have hinv : (1 : ℝ) / ((1 / 16 : ℝ) * Real.log (r : ℝ)) =
      16 / Real.log (r : ℝ) := by field_simp
  rw [hinv] at hm
  have hcond := conditional_inverse_contacts_known R L Q ξ₀ out hs H hD
  filter_upwards [hcond] with ξ hξ hhist
  rw [hξ hhist]
  simpa only [one_div] using hm

end
end FiniteAvalanches.Wilson.Lattice.CurrentCompletedContraction
