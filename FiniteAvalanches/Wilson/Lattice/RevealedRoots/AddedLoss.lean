import FiniteAvalanches.Wilson.Lattice.LocalComparison.FullExpectation
import FiniteAvalanches.Wilson.Lattice.LocalComparison.AnnulusHitting
import FiniteAvalanches.RevealedRoots.ExpectedContactLoss

set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.Revealed19
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteWired FiniteAvalanches.Needle FiniteAvalanches.RevealedRoots MeasureTheory
open scoped Classical BigOperators ENNReal
noncomputable section

/-- The same zero sites in the original active-vertex carrier. -/
def activeZeros (N : ℕ) (Z : Finset (Site 2)) : Finset (Active N) :=
  Finset.univ.filter (fun x => site x ∈ Z)

theorem activeZeros_image (N : ℕ) (Z : Finset (Site 2))
    (hZ : (Z : Set (Site 2)) ⊆ box 2 N) : (activeZeros N Z).image site = Z := by
  ext x
  constructor
  · rintro hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hy).2
  · intro hx
    have hi : inBox N x := (inBox_iff N x).mpr (hZ hx)
    exact Finset.mem_image.mpr ⟨activeOfSite N x hi,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [site_activeOfSite] using hx⟩,
      site_activeOfSite N x hi⟩

/-- The full observable has literal finite support when its origin set is finite. -/
theorem full_finite (F : Finset (Site 2)) (σ : ColorField) :
    LocalFullContacts.full (F : Set (Site 2)) σ = (contacts F σ : ℝ≥0∞) := by
  rw [LocalFullContacts.full, tsum_eq_sum (s := F) (by
    intro x hx
    exact if_neg hx), LocalFullContacts.cast_contacts]
  apply Finset.sum_congr rfl
  intro x hx
  rw [if_pos (show x ∈ (F : Set (Site 2)) from hx)]

theorem added_set (R : RootPair) (K Z : Finset (Site 2))
    (hR : R.zero = ((K ∪ Z : Finset (Site 2)) : Set (Site 2))) :
    R.zero \ (K : Set (Site 2)) = (Z \ K : Finset (Site 2)) := by
  rw [hR]
  ext x
  simp only [Set.mem_sdiff, Finset.mem_coe, Finset.mem_union, Finset.mem_sdiff]
  tauto

/-- No off-support convention is used: the entire added-root count is finite everywhere. -/
theorem added_full_finite_integrable (R : RootPair) (K Z : Finset (Site 2))
    (hR : R.zero = ((K ∪ Z : Finset (Site 2)) : Set (Site 2))) :
    (∀ σ, LocalFullContacts.full (R.zero \ (K : Set (Site 2))) σ =
      (contacts (Z \ K) σ : ℝ≥0∞)) ∧
    (∀ σ, LocalFullContacts.full (R.zero \ (K : Set (Site 2))) σ ≠ ⊤) ∧
    Integrable (fun σ => (LocalFullContacts.full (R.zero \ (K : Set (Site 2))) σ).toReal)
      (wilsonColorLaw R) := by
  have he (σ : ColorField) := full_finite (Z \ K) σ
  rw [← added_set R K Z hR] at he
  refine ⟨he, fun σ => (he σ) ▸ ENNReal.natCast_ne_top _, ?_⟩
  have hf : (fun σ => (LocalFullContacts.full (R.zero \ (K : Set (Site 2))) σ).toReal) =
      (fun σ => (contacts (Z \ K) σ : ℝ)) := by
    funext σ
    rw [he, ENNReal.toReal_natCast]
  rw [hf]
  exact LocalFullExpectation.integrable_contacts R (Z \ K)

/-- First-hit ordering uses the actual nonstopping convention. -/
theorem firstHit_event (A C : Set (Site 2)) (y : Site 2) :
    {w | firstHit C (position y w) < firstHit A (position y w)} = hitBefore A C y := by
  ext w
  exact (hitBefore_iff_firstHit_lt A C y w).symm

/-- Once per original lattice incidence, on an arbitrary actual active zero set. -/
theorem hitting_sum_conductance (N : ℕ) (S : Finset (Active N)) :
    (∑ x ∈ S.image site, ∑ y ∈ nbrFinset x, walkLaw
      {w | firstHit (box 2 N)ᶜ (position y w) <
        firstHit (S.image site : Set (Site 2)) (position y w)}) =
      ENNReal.ofReal (wiredConductance N S) := by
  simp_rw [firstHit_event, hitting_eq_potential,
    ← ENNReal.ofReal_sum_of_nonneg (fun y _ => potential_nonneg N S y)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ =>
    Finset.sum_nonneg (fun y _ => potential_nonneg N S y))]
  congr 1
  rw [Finset.sum_image]
  · exact zero_contact_sum_eq_conductance N S
  · exact fun x _ y _ hxy => site_injective N hxy

/-- Original copied-edge first-exit probabilities sum to the literal wired conductance. -/
theorem firstExit_sum (N : ℕ) (Z : Finset (Site 2))
    (hZ : (Z : Set (Site 2)) ⊆ box 2 N) :
    (∑ x ∈ Z, ∑ y ∈ nbrFinset x, walkLaw
      {w | firstHit (box 2 N)ᶜ (position y w) < firstHit (Z : Set (Site 2)) (position y w)}) =
      ENNReal.ofReal (wiredConductance N (activeZeros N Z)) := by
  conv_lhs => rw [← activeZeros_image N Z hZ]
  exact hitting_sum_conductance N (activeZeros N Z)

/-- Full added-root loss, derived from the actual marginal and all original incidences. -/
theorem added_mean_le_conductance (R : RootPair) (K Z : Finset (Site 2)) (N : ℕ)
    (hR : R.zero = ((K ∪ Z : Finset (Site 2)) : Set (Site 2)))
    (hZ : (Z : Set (Site 2)) ⊆ box 2 N) (hC : R.one ⊆ (box 2 N)ᶜ) :
    (∫ σ, (contacts (Z \ K) σ : ℝ) ∂wilsonColorLaw R) ≤
      wiredConductance N (activeZeros N Z) := by
  have hZR : (Z : Set (Site 2)) ⊆ R.zero := by
    rw [hR]
    exact fun _ hx => Finset.mem_union_right K hx
  have hb := added_contacts_expectation_le_firstExit R K Z N hZR hC
  rw [firstExit_sum N Z hZ] at hb
  have hint := LocalFullExpectation.integrable_contacts R (Z \ K)
  have he : (∫ σ, (contacts (Z \ K) σ : ℝ) ∂wilsonColorLaw R) =
      (∫⁻ σ, (contacts (Z \ K) σ : ℝ≥0∞) ∂wilsonColorLaw R).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun _ => Nat.cast_nonneg _))
      hint.aestronglyMeasurable]
    congr 1
    apply lintegral_congr
    intro σ
    simp only [ENNReal.ofReal_natCast]
  rw [he]
  have hb' : (∫⁻ σ, (contacts (Z \ K) σ : ℝ≥0∞) ∂wilsonColorLaw R) ≤
      ENNReal.ofReal (wiredConductance N (activeZeros N Z)) := by
    simp_rw [LocalFullContacts.cast_contacts]
    exact hb
  exact ((ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb')
    ENNReal.ofReal_ne_top).mpr hb').trans_eq
    (ENNReal.toReal_ofReal (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- The literal107 needle budget controls the full real expectation. -/
theorem added_mean_le_107 (R : RootPair) (K Z : Finset (Site 2)) (h : ℕ)
    (hR : R.zero = ((K ∪ Z : Finset (Site 2)) : Set (Site 2)))
    (hZ : (Z : Set (Site 2)) ⊆ box 2 (2*h)) (hC : R.one ⊆ (box 2 (2*h))ᶜ)
    (hbudget : wiredConductance (2*h) (activeZeros (2*h) Z) ≤ 107*Real.log h) :
    (∀ σ, LocalFullContacts.full (R.zero \ (K : Set (Site 2))) σ ≠ ⊤) ∧
    Integrable (fun σ => (LocalFullContacts.full (R.zero \ (K : Set (Site 2))) σ).toReal)
      (wilsonColorLaw R) ∧
    (∫ σ, (LocalFullContacts.full (R.zero \ (K : Set (Site 2))) σ).toReal
      ∂wilsonColorLaw R) ≤ 107*Real.log h := by
  obtain ⟨he,hfinite,hint⟩ := added_full_finite_integrable R K Z hR
  refine ⟨hfinite,hint,?_⟩
  simp_rw [he, ENNReal.toReal_natCast]
  exact (added_mean_le_conductance R K Z (2*h) hR hZ hC).trans hbudget

end
end FiniteAvalanches.Wilson.Lattice.Revealed19
