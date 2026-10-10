import FiniteAvalanches.Wilson.Lattice.LocalComparison.LossBound
import FiniteAvalanches.Wilson.Lattice.ReciprocalContactMonotonicity

set_option autoImplicit false
namespace LocalFullExpectation
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.Lattice MeasureTheory
open scoped Classical ENNReal
noncomputable section

/-- Every finite all-incidence contact count is integrable under the actual Wilson law. -/
theorem integrable_contacts (R : RootPair) (K : Finset (Site 2)) :
    Integrable (fun σ => (contacts K σ : ℝ)) (wilsonColorLaw R) := by
  apply (integrable_const (4*(K.card : ℝ))).mono'
    (((continuous_of_discreteTopology : Continuous (fun n : ℕ => (n : ℝ))).comp
      (continuous_contacts K)).measurable.aestronglyMeasurable)
  apply ae_of_all
  intro σ
  rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
  change (contacts K σ : ℝ) ≤ 4*(K.card : ℝ)
  exact_mod_cast contacts_le_four_mul_card K σ

/-- Full support gives integrability of the entire count, rather than a truncation premise. -/
theorem integrable_full (D : Finset (Site 2))
    (P : FiniteAvalanches.Electrical.Plane.SourceLattice.OneSet D)
    (A : Set (Site 2)) (N : ℕ)
    (hD : (D : Set (Site 2)) ⊆ (boxSites N : Set (Site 2))) :
    Integrable (fun σ => (LocalFullContacts.full A σ).toReal)
      (wilsonColorLaw (LocalZeroExterior.domainRoots D P)) := by
  have he : (fun σ => (LocalFullContacts.full A σ).toReal) =ᵐ[wilsonColorLaw (LocalZeroExterior.domainRoots D P)]
      (fun σ => (localContacts A 0 (N+1) σ : ℝ)) := by
    filter_upwards [LocalFullContacts.ae_support D P] with σ hσ
    rw [LocalFullContacts.full_eq_window D A N hD σ hσ,ENNReal.toReal_natCast]
  exact (integrable_congr he).mpr (integrable_contacts _ _)

/-- The proved nonnegative full-count bound also holds for the real expectation. -/
theorem real_expectation_le_sixteen (r : ℕ) (hr : 1 ≤ r)
    (D : Finset (Site 2)) (P : FiniteAvalanches.Electrical.Plane.SourceLattice.OneSet D)
    (A : Set (Site 2))
    (hDbox : (D : Set (Site 2)) ⊆ (boxSites (2*r-1) : Set (Site 2)))
    (hPbox : (P.val.image Subtype.val : Set (Site 2)) ⊆ (boxSites r : Set (Site 2)))
    (hExit : ∀ y ∈ D, ∀ x, x ∉ D → x ∉ A → (lattice 2).Adj y x → x ∉ boxSites (2*r-1)) :
    (∫ σ, (LocalFullContacts.full ((D : Set (Site 2))ᶜ \ A) σ).toReal
      ∂wilsonColorLaw (LocalZeroExterior.domainRoots D P)) ≤ 16 := by
  let R := LocalZeroExterior.domainRoots D P
  have hfinite : ∀ᵐ σ ∂wilsonColorLaw R,
      LocalFullContacts.full ((D : Set (Site 2))ᶜ \ A) σ ≠ ⊤ := by
    filter_upwards [LocalFullContacts.ae_support D P] with σ hσ
    rw [LocalFullContacts.full_eq_window D ((D : Set (Site 2))ᶜ \ A) (2*r-1) hDbox σ hσ]
    exact ENNReal.natCast_ne_top _
  have he : (∫ σ, (LocalFullContacts.full ((D : Set (Site 2))ᶜ \ A) σ).toReal ∂wilsonColorLaw R) =
      (∫⁻ σ, LocalFullContacts.full ((D : Set (Site 2))ᶜ \ A) σ ∂wilsonColorLaw R).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun _ => ENNReal.toReal_nonneg))
      (integrable_full D P _ (2*r-1) hDbox).aestronglyMeasurable]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [hfinite] with σ hσ
    exact ENNReal.ofReal_toReal hσ
  rw [he]
  have hb := LocalLossBound.expectation_le_sixteen r hr D P A hDbox hPbox hExit
  exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top (by norm_num) hb) (by norm_num)).mpr hb

end
end LocalFullExpectation
