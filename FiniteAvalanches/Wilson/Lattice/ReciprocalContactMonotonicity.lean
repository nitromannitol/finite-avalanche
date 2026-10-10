import FiniteAvalanches.Wilson.Lattice.ColorMonotonicity
import FiniteAvalanches.Wilson.Lattice.ForestEvents
import Mathlib.MeasureTheory.Integral.Layercake
import LatticeProb.Graph.Zd

/-! Expectation comparison for the literal all-neighbor contact count. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice
open LatticeProb FiniteAvalanches.Sandpile MeasureTheory
open scoped Classical
noncomputable section

/-- Every original neighbor occurrence contributes at most one. -/
theorem contacts_le_four_mul_card (K : Finset (Site 2)) (σ : ColorField) :
    contacts K σ ≤ 4 * K.card := by
  calc
    contacts K σ ≤ ∑ x ∈ K, ∑ _y ∈ nbrFinset x, 1 := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      cases σ y <;> simp only [Bool.false_eq_true, ↓reduceIte, zero_le, le_refl]
    _ = 4 * K.card := by
      simp only [Finset.sum_const, smul_eq_mul, mul_one, Graph.Zd.card_nbrFinset]
      omega

/-- Enlarging the one-colored sites in the contact window enlarges the count. -/
theorem contacts_mono_on_contactSites (K : Finset (Site 2)) {σ τ : ColorField}
    (h : ∀ y ∈ contactSites K, σ y = true → τ y = true) :
    contacts K σ ≤ contacts K τ := by
  apply Finset.sum_le_sum
  intro x hx
  apply Finset.sum_le_sum
  intro y hy
  have hst := h y (Finset.mem_biUnion.mpr ⟨x, hx, hy⟩)
  cases hs : σ y <;> cases ht : τ y <;> simp_all only [Bool.false_eq_true,
    ↓reduceIte, zero_le, le_refl]

/-- An actual adjacent one-root supplies positivity almost everywhere. -/
theorem contacts_ge_one_ae_of_adjacent_one_root (R : RootPair)
    (K : Finset (Site 2)) (k b : Site 2) (hk : k ∈ K) (hb : b ∈ R.one)
    (hadj : (lattice 2).Adj k b) :
    ∀ᵐ σ ∂wilsonColorLaw R, 1 ≤ contacts K σ := by
  have hc : ∀ᵐ σ ∂wilsonColorLaw R, σ b = true := by
    rw [wilsonColorLaw]
    apply (ae_map_iff measurable_snd.aemeasurable
      ((isClosed_singleton.preimage (continuous_apply b)).measurableSet)).mpr
    filter_upwards [wilsonLaw_ae_root_colors R] with ω hω
    exact hω.1 b hb
  filter_upwards [hc] with σ hσ
  have hy : b ∈ nbrFinset k := (FiniteWired.mem_neighbors_iff k b).mpr hadj
  have hi := Finset.single_le_sum (fun y (_ : y ∈ nbrFinset k) =>
    Nat.zero_le (if σ y then 1 else 0)) hy
  have ho := Finset.single_le_sum (fun x (_ : x ∈ K) =>
    Nat.zero_le (∑ y ∈ nbrFinset x, if σ y then 1 else 0)) hk
  simp only [hσ, ↓reduceIte] at hi
  exact hi.trans ho

private def reciprocalComplement (n : ℕ) : ℝ := 1 - 1 / (max 1 n : ℕ)

private theorem reciprocalComplement_nonneg (n : ℕ) : 0 ≤ reciprocalComplement n := by
  have h : (1 : ℝ) ≤ (max 1 n : ℕ) := by exact_mod_cast (le_max_left 1 n)
  have hd : (1 : ℝ) / (max 1 n : ℕ) ≤ 1 := (div_le_one (by linarith)).mpr h
  exact sub_nonneg.mpr hd

private theorem reciprocalComplement_le_one (n : ℕ) : reciprocalComplement n ≤ 1 :=
  sub_le_self _ (by positivity)

private theorem reciprocalComplement_mono : Monotone reciprocalComplement := by
  intro m n hmn
  have hm : (0 : ℝ) < (max 1 m : ℕ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 m))
  have hmn' : (max 1 m : ℕ) ≤ (max 1 n : ℕ) := max_le_max_left 1 hmn
  have hd : (1 : ℝ) / (max 1 n : ℕ) ≤ 1 / (max 1 m : ℕ) :=
    one_div_le_one_div_of_le hm (Nat.cast_le.mpr hmn')
  exact sub_le_sub_left hd 1

private theorem integrable_reciprocalComplement (R : RootPair) (K : Finset (Site 2)) :
    Integrable (fun σ => reciprocalComplement (contacts K σ)) (wilsonColorLaw R) := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact ((continuous_of_discreteTopology : Continuous reciprocalComplement).comp
      (continuous_contacts K)).measurable.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun σ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (reciprocalComplement_nonneg _)]
      exact reciprocalComplement_le_one _)

/-- The actual reciprocal is bounded and measurable even on zero-count fields. -/
theorem integrable_reciprocal_contacts (R : RootPair) (K : Finset (Site 2)) :
    Integrable (fun σ => (1 : ℝ) / (contacts K σ : ℝ)) (wilsonColorLaw R) := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact ((continuous_of_discreteTopology : Continuous (fun n : ℕ => (1 : ℝ) / n)).comp
      (continuous_contacts K)).measurable.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun σ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    by_cases h : contacts K σ = 0
    · simp only [h, Nat.cast_zero, div_zero, zero_le_one]
    · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero h)).mpr
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h)

private def extendContactPattern (K : Finset (Site 2)) (p : contactSites K → Bool) :
    ColorField := fun y => if hy : y ∈ contactSites K then p ⟨y, hy⟩ else false

private theorem contacts_extend_restrict (K : Finset (Site 2)) (σ : ColorField) :
    contacts K (extendContactPattern K (fun y => σ y.val)) = contacts K σ := by
  apply contacts_of_agree
  intro y hy
  simp only [extendContactPattern, dif_pos hy]

private theorem reciprocalComplement_tail_mono (R Q : RootPair)
    (hz : Q.zero = R.zero) (ho : Q.one ⊆ R.one) (K : Finset (Site 2)) (t : ℝ) :
    wilsonColorLaw Q {σ | t < reciprocalComplement (contacts K σ)} ≤
      wilsonColorLaw R {σ | t < reciprocalComplement (contacts K σ)} := by
  let H : Set (contactSites K → Bool) :=
    {p | t < reciprocalComplement (contacts K (extendContactPattern K p))}
  have hH : ∀ p ∈ H, ∀ q : contactSites K → Bool,
      (∀ x, p x = true → q x = true) → q ∈ H := by
    intro p hp q hpq
    change t < reciprocalComplement (contacts K (extendContactPattern K p)) at hp
    change t < reciprocalComplement (contacts K (extendContactPattern K q))
    apply lt_of_lt_of_le hp
    apply reciprocalComplement_mono
    apply contacts_mono_on_contactSites
    intro y hy hpy
    simp only [extendContactPattern, dif_pos hy] at hpy ⊢
    exact hpq ⟨y, hy⟩ hpy
  have he : windowColorEvent (contactSites K) H =
      {σ | t < reciprocalComplement (contacts K σ)} := by
    ext σ
    change (t < reciprocalComplement
      (contacts K (extendContactPattern K (fun y => σ y.val)))) ↔ _
    rw [contacts_extend_restrict]
    rfl
  have h := color_window_one_roots_removed R Q hz ho (contactSites K) H hH
  rw [he] at h
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp h

private theorem integral_reciprocalComplement_mono (R Q : RootPair)
    (hz : Q.zero = R.zero) (ho : Q.one ⊆ R.one) (K : Finset (Site 2)) :
    (∫ σ, reciprocalComplement (contacts K σ) ∂wilsonColorLaw Q) ≤
      ∫ σ, reciprocalComplement (contacts K σ) ∂wilsonColorLaw R := by
  have hnn (S : RootPair) :
      0 ≤ᵐ[wilsonColorLaw S] (fun σ => reciprocalComplement (contacts K σ)) :=
    Filter.Eventually.of_forall (fun σ => reciprocalComplement_nonneg _)
  have hi (S : RootPair) := integrable_reciprocalComplement S K
  rw [integral_eq_lintegral_of_nonneg_ae (hnn Q) (hi Q).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (hnn R) (hi R).aestronglyMeasurable]
  apply ENNReal.toReal_mono (hi R).lintegral_lt_top.ne
  rw [lintegral_eq_lintegral_meas_lt _ (hnn Q) (hi Q).aemeasurable,
    lintegral_eq_lintegral_meas_lt _ (hnn R) (hi R).aemeasurable]
  exact lintegral_mono (fun t => reciprocalComplement_tail_mono R Q hz ho K t)

/-- With fixed zero roots, enlarging the actual one roots decreases the expectation
of the literal reciprocal contact count. The adjacent one-root supplies positivity. -/
theorem integral_reciprocal_contacts_one_roots_mono (Q R : RootPair)
    (K : Finset (Site 2)) (hQ : Q.zero = (K : Set (Site 2)))
    (hR : R.zero = (K : Set (Site 2))) (ho : Q.one ⊆ R.one)
    (k b : Site 2) (hk : k ∈ K) (hb : b ∈ Q.one) (hadj : (lattice 2).Adj k b) :
    (∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw R) ≤
      ∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw Q := by
  have hp (S : RootPair) (hs : b ∈ S.one) :
      (∫ σ, reciprocalComplement (contacts K σ) ∂wilsonColorLaw S) =
        1 - ∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw S := by
    calc
      _ = ∫ σ, (1 : ℝ) - (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw S := by
        apply integral_congr_ae
        filter_upwards [contacts_ge_one_ae_of_adjacent_one_root S K k b hk hs hadj]
          with σ hσ
        simp only [reciprocalComplement, max_eq_right hσ]
      _ = _ := by
        rw [integral_sub (integrable_const (1 : ℝ)) (integrable_reciprocal_contacts S K),
          integral_const, probReal_univ, one_smul]
  have h := integral_reciprocalComplement_mono R Q (hQ.trans hR.symm) ho K
  rw [hp Q hb, hp R (ho hb)] at h
  linarith only [h]

end
end FiniteAvalanches.Wilson.Lattice
