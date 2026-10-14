import FiniteAvalanches.Wilson.Lattice.UnconditionalInverseRecurrence
import FiniteAvalanches.Probability.Multiscale.FiniteHorizonForcing
import FiniteAvalanches.Probability.Multiscale.MaximalSourceScale
import FiniteAvalanches.Wilson.Lattice.CofiniteReciprocalGeometry

/-! Incoming c0c29619 (forest proof unchanged through parents 593e2a25 and cd552a5), main.tex 504–534: the unconditional decreasing inverse
means, their consecutive-scale iteration, and the full logarithmic exponent. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.CurrentForestReciprocal
open LatticeProb Sandpile MeasureTheory Filter
open Probability.CurrentScale Probability.CurrentRecurrence CurrentNestedPrefix
open CurrentUnconditionalInverse CurrentInverseContraction CofiniteReciprocalGeometry Translation
open scoped Classical
noncomputable section

theorem zero_mem_sourceWindow (K : Finset (Site 2)) (h0 : (0 : Site 2) ∈ K)
    (b i : ℕ) : (0 : Site 2) ∈ sourceWindow K b i := by
  apply Finset.mem_filter.mpr
  refine ⟨h0, ?_⟩
  apply Finset.sup_le
  intro j _hj
  simp only [Pi.zero_apply, sub_self, Int.natAbs_zero]
  exact Nat.zero_le _

theorem inverse_mean_le_one (R : RootPair) (F : Finset (Site 2)) :
    (∫ σ, (contacts F σ : ℝ)⁻¹ ∂wilsonColorLaw R) ≤ 1 := by
  have hI : Integrable (fun σ => (contacts F σ : ℝ)⁻¹) (wilsonColorLaw R) := by
    simpa only [one_div] using integrable_reciprocal_contacts R F
  have hm := integral_mono_ae hI (integrable_const (1 : ℝ))
    (Eventually.of_forall (fun σ => nat_inverse_le_one (contacts F σ)))
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hm

/-- For the actual one-root law, enlarging the original origin window decreases
the reciprocal mean. Positivity is derived from the literal neighboring root. -/
theorem inverse_mean_mono_origins (R : RootPair) (F H : Finset (Site 2))
    (hFH : F ⊆ H) (hF0 : (0 : Site 2) ∈ F)
    (hadj : ∃ y ∈ R.one, (lattice 2).Adj 0 y) :
    (∫ σ, (contacts H σ : ℝ)⁻¹ ∂wilsonColorLaw R) ≤
      ∫ σ, (contacts F σ : ℝ)⁻¹ ∂wilsonColorLaw R := by
  obtain ⟨y, hy, hadj⟩ := hadj
  have hpos := contacts_ge_one_ae_of_adjacent_one_root R F 0 y hF0 hy hadj
  have hIF : Integrable (fun σ => (contacts F σ : ℝ)⁻¹) (wilsonColorLaw R) := by
    simpa only [one_div] using integrable_reciprocal_contacts R F
  have hIH : Integrable (fun σ => (contacts H σ : ℝ)⁻¹) (wilsonColorLaw R) := by
    simpa only [one_div] using integrable_reciprocal_contacts R H
  apply integral_mono_ae hIH hIF
  filter_upwards [hpos] with σ hσ
  have hFpos : (0 : ℝ) < contacts F σ := by exact_mod_cast (by omega : 0 < contacts F σ)
  exact inv_anti₀ hFpos (Nat.cast_le.mpr (contacts_mono_origins hFH σ))

/-- The incoming source sequence consists of the genuine, decreasing reciprocal
means of the nested finite windows, with their original all-neighbor contacts. -/
theorem source_inverse_mean_antitone (R : RootPair) (K : Finset (Site 2))
    (h0 : (0 : Site 2) ∈ K) (hadj : ∃ y ∈ R.one, (lattice 2).Adj 0 y)
    (b : ℕ) (hb : 6 ≤ b) :
    Antitone (fun i => ∫ σ, (contacts (sourceWindow K b i) σ : ℝ)⁻¹ ∂wilsonColorLaw R) := by
  intro i j hij
  apply inverse_mean_mono_origins R _ _ _ (zero_mem_sourceWindow K h0 b i) hadj
  intro x hx
  obtain ⟨hxK, hxrad⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hxK,
    hxrad.trans (Nat.mul_le_mul_left 3 (scale_mono b hb hij))⟩

/-- Current consecutive inverse-mean proof at the origin, with a positive
universal constant and the full exponent -log(1-epsilon/2)/log(6*kappa). -/
theorem origin_forest_reciprocal :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ K : Finset (Site 2),
      ((lattice 2).induce (K : Set (Site 2))).Connected →
      ∀ γ : Set (Site 2), ((lattice 2).induce γ).Connected → γᶜ.Finite →
        Disjoint (K : Set (Site 2)) γ → (0 : Site 2) ∈ K →
        (∃ y ∈ γ, (lattice 2).Adj 0 y) →
      ∀ R : RootPair, R.zero = (K : Set (Site 2)) → R.one = γ →
        (∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw R) ≤
          C * Real.rpow (Real.log (((K.sup (fun x => K.sup (fun y => siteRadius x y)) : ℕ) : ℝ) + 2)) (-a) := by
  obtain ⟨ε, hε, hεsmall, κ, hκ, _hpaid, D, hD, hrec⟩ := source_inverse_mean_recurrence
  let b := 6 * κ
  let q : ℝ := 1 - ε / 2
  have hb : 6 ≤ b := by dsimp only [b]; omega
  have hqlo : (1 / 2 : ℝ) < q := by dsimp only [q]; linarith
  have hqhi : q < 1 := by dsimp only [q]; linarith
  obtain ⟨A, hA, hforcing⟩ := source_forcing_le_geometric b hb D hD.le
  obtain ⟨C₁, hC₁, hiterate⟩ := geometric_forcing_bound_finite b hb q A hqlo hA.le
  obtain ⟨ha, C₂, hC₂, hlarge, hsmall⟩ := maximal_scale_log_bound b hb q hqlo hqhi
  refine ⟨exponent b q, (C₁ + 1) * C₂, ha, mul_pos (by linarith) hC₂, ?_⟩
  intro K hK γ hγ hfin hd h0 hadj R hz ho
  let d := K.sup (fun x => K.sup (fun y => siteRadius x y))
  have hrootadj : ∃ y ∈ R.one, (lattice 2).Adj 0 y := by rwa [ho]
  have hpow : 0 ≤ Real.rpow (Real.log ((d : ℝ) + 2)) (-(exponent b q)) :=
    (Real.rpow_pos_of_pos (log_diameter_pos d) _).le
  change (∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw R) ≤
    ((C₁ + 1) * C₂) * Real.rpow (Real.log ((d : ℝ) + 2)) (-(exponent b q))
  by_cases hdiam : 16 * scale b 2 ≤ d
  · obtain ⟨n, hn, hdn, hdnext⟩ := exists_maximal_source_scale b hb d hdiam
    let u : ℕ → ℝ := fun i => ∫ σ, (contacts (sourceWindow K b i) σ : ℝ)⁻¹ ∂wilsonColorLaw R
    have hu1 : u 1 ≤ 1 := inverse_mean_le_one R _
    have hurec : ∀ i : ℕ, 2 ≤ i → i ≤ n → u i ≤ q * u (i - 1) + A / (b : ℝ) ^ i := by
      intro i hi hin
      have hm := hrec K γ hK h0 hd hγ hfin hadj R hz ho n hn hdn i hi hin
      have hf := hforcing i hi
      change u i ≤ q * u (i - 1) + 16 / Real.log (scale b i : ℝ) +
        D * Real.rpow (scale b (i - 1) : ℝ) (-(1 / 2 : ℝ)) at hm
      calc
        u i ≤ q * u (i - 1) + 16 / Real.log (scale b i : ℝ) +
            D * Real.rpow (scale b (i - 1) : ℝ) (-(1 / 2 : ℝ)) := hm
        _ = q * u (i - 1) + (16 / Real.log (scale b i : ℝ) +
            D * Real.rpow (scale b (i - 1) : ℝ) (-(1 / 2 : ℝ))) := by ring
        _ ≤ q * u (i - 1) + A / (b : ℝ) ^ i := add_le_add le_rfl hf
    have hu := hiterate u n (by omega) hu1 hurec
    have hmono := inverse_mean_mono_origins R (sourceWindow K b n) K
      (Finset.filter_subset _ _) (zero_mem_sourceWindow K h0 b n) hrootadj
    have hlog := hlarge d n hn hdn hdnext
    calc
      (∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw R) ≤ u n := by
        simpa only [one_div] using hmono
      _ ≤ C₁ * q ^ n := hu
      _ ≤ C₁ * (C₂ * Real.rpow (Real.log ((d : ℝ) + 2)) (-(exponent b q))) :=
        mul_le_mul_of_nonneg_left hlog hC₁.le
      _ ≤ ((C₁ + 1) * C₂) * Real.rpow (Real.log ((d : ℝ) + 2)) (-(exponent b q)) := by
        have hm := mul_nonneg hC₂.le hpow
        nlinarith
  · have hs := hsmall d (Nat.lt_of_not_ge hdiam)
    calc
      (∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw R) ≤ 1 := by
        simpa only [one_div] using inverse_mean_le_one R K
      _ ≤ C₂ * Real.rpow (Real.log ((d : ℝ) + 2)) (-(exponent b q)) := hs
      _ ≤ ((C₁ + 1) * C₂) * Real.rpow (Real.log ((d : ℝ) + 2)) (-(exponent b q)) := by
        have hm := mul_nonneg hC₂.le hpow
        nlinarith

/-- Whole-site translation gives the exact current forest reciprocal statement.
Only the incoming consecutive inverse-mean proof is used in the body. -/
theorem forest_reciprocal_cofinite_current :
    ∃ a C : ℝ, 0 < a ∧ ∀ K : Finset (Site 2),
      ((lattice 2).induce (K : Set (Site 2))).Connected →
      ∀ γ : Set (Site 2), ((lattice 2).induce γ).Connected → γᶜ.Finite →
        Disjoint (K : Set (Site 2)) γ →
        (∃ k ∈ K, ∃ y ∈ γ, (lattice 2).Adj k y) →
      ∀ R : RootPair, R.zero = (K : Set (Site 2)) → R.one = γ →
        (∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw R) ≤
          C * Real.rpow (Real.log (((K.sup (fun x => K.sup (fun y => siteRadius x y)) : ℕ) : ℝ) + 2)) (-a) := by
  obtain ⟨a, C, ha, _hC, horigin⟩ := origin_forest_reciprocal
  refine ⟨a, C, ha, ?_⟩
  intro K hK γ hγ hfin hd hadj R hz ho
  obtain ⟨k, hk, y, hy, hky⟩ := hadj
  let z := -k
  let K' := finiteSet K z
  let γ' : Set (Site 2) := {x | x - z ∈ γ}
  have hK' : ((lattice 2).induce (K' : Set (Site 2))).Connected := connected_translate K z hK
  have hγ' : ((lattice 2).induce γ').Connected := connected_set_translate γ z hγ
  have hfin' : γ'ᶜ.Finite := cofinite_set_translate γ z hfin
  have hd' : Disjoint (K' : Set (Site 2)) γ' := by
    apply Set.disjoint_left.mpr
    intro x hx hy'
    exact Set.disjoint_left.mp hd ((mem_finiteSet K z x).mp hx) hy'
  have h0' : (0 : Site 2) ∈ K' := Finset.mem_image.mpr ⟨k, hk, add_neg_cancel k⟩
  have hadj' : ∃ y ∈ γ', (lattice 2).Adj 0 y := by
    refine ⟨y + z, ?_, ?_⟩
    · change y + z - z ∈ γ
      rwa [add_sub_cancel_right]
    · have hm := (adjacency_add k y z).mpr hky
      simpa only [z, add_neg_cancel] using hm
  obtain ⟨hz', ho'⟩ := roots_translate_source R K γ z hz ho
  have hm := horigin K' hK' γ' hγ' hfin' hd' h0' hadj' (roots R z) hz' ho'
  change (∫ σ, (1 : ℝ) / (contacts (finiteSet K z) σ : ℝ) ∂wilsonColorLaw (roots R z)) ≤
    C * Real.rpow (Real.log
      ((((finiteSet K z).sup (fun x => (finiteSet K z).sup (fun y => siteRadius x y)) : ℕ) : ℝ) + 2)) (-a) at hm
  rwa [reciprocal_expectation_translate, diameter_translate] at hm

end
end FiniteAvalanches.Wilson.Lattice.CurrentForestReciprocal
