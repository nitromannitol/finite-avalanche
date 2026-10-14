import FiniteAvalanches.Needle.Direct.RadialTwelve
import FiniteAvalanches.Wilson.Lattice.LocalComparison.FullExpectation
import FiniteAvalanches.Wilson.Lattice.LocalComparison.ComponentIdentification

/-! The full unwanted-contact mean in incoming cd552a5, main.tex lines 432–436.
The radial numerical bound uses the literal original-copy wired square.
The Wilson law retains its registered standard input. -/

set_option autoImplicit false

open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.Lattice MeasureTheory
open FiniteAvalanches.Electrical.Plane.SourceLattice
open scoped Classical ENNReal

noncomputable section

namespace LocalLossBound

/-- The natural source distance and integer radial cutoff specify the same square. -/
theorem site_radius_zero_le_iff_box (x : Site 2) (r : ℕ) :
    siteRadius 0 x ≤ r ↔ x ∈ box 2 r := by
  rw [FiniteAvalanches.Needle.mem_box_iff, FiniteAvalanches.Needle.radius_le_iff]
  simpa only [Pi.zero_apply, sub_zero] using siteRadius_le_iff 0 x r

/-- Equality on the actual active carrier, rather than an assumed voltage dictionary. -/
theorem inner_eq_radial_square (r : ℕ) :
    inner r = Finset.univ.filter (fun x : FiniteWired.Active (2*r-1) =>
      FiniteWired.site x ∈ box 2 r) := by
  ext x
  simp only [inner, Finset.mem_filter, Finset.mem_univ, true_and]
  exact site_radius_zero_le_iff_box (FiniteWired.site x) r

/-- The source annulus uses the exact twelve-energy radial trial. -/
theorem annulus_conductance_le_twelve (r : ℕ) (hr : 1 ≤ r) :
    FiniteAvalanches.Needle.wiredConductance (2*r-1) (inner r) ≤ 12 := by
  rw [inner_eq_radial_square]
  exact FiniteAvalanches.Needle.CurrentRadial.radial_conductance_le_twelve r hr

                                                                  
                                                                                   
theorem expectation_le_twelve (r : ℕ) (hr : 1 ≤ r)
    (D : Finset (Site 2)) (P : OneSet D) (A : Set (Site 2))
    (hDbox : (D : Set (Site 2)) ⊆ (boxSites (2*r-1) : Set (Site 2)))
    (hPbox : (P.val.image Subtype.val : Set (Site 2)) ⊆ (boxSites r : Set (Site 2)))
    (hExit : ∀ y ∈ D, ∀ x, x ∉ D → x ∉ A → (lattice 2).Adj y x →
      x ∉ boxSites (2*r-1)) :
    (∫⁻ σ, LocalFullContacts.full ((D : Set (Site 2))ᶜ \ A) σ
      ∂wilsonColorLaw (LocalZeroExterior.domainRoots D P)) ≤ 12 := by
  let K := unwantedWindow r D A
  let O := LocalAnnulusCopies.outerSites (2*r-1)
  let R := LocalZeroExterior.domainRoots D P
  rw [full_expectation_eq_hitting r hr D P A hDbox]
  calc
    _ = ∑ x ∈ K ∩ O, ∑ y ∈ nbrFinset x, walkLaw (hitBefore R.zero R.one y) := by
      apply (Finset.sum_subset Finset.inter_subset_left ?_).symm
      intro x hx hxKO
      exact unwanted_sum_zero_off_annulus r D P A hDbox hExit x hx
        (fun hxO => hxKO (Finset.mem_inter.mpr ⟨hx, hxO⟩))
    _ ≤ ∑ x ∈ K ∩ O, ∑ y ∈ nbrFinset x,
        walkLaw (hitBefore (boxSites (2*r-1) : Set (Site 2))ᶜ (boxSites r) y) :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ =>
        domain_hitting_le_annulus r D P hDbox hPbox y))
    _ ≤ ∑ x ∈ O, ∑ y ∈ nbrFinset x,
        walkLaw (hitBefore (boxSites (2*r-1) : Set (Site 2))ᶜ (boxSites r) y) :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun _ _ _ => bot_le)
    _ = ENNReal.ofReal (FiniteAvalanches.Needle.wiredConductance (2*r-1) (inner r)) :=
      annulus_hitting_sum r hr
    _ ≤ 12 := by
      exact (ENNReal.ofReal_le_ofReal (annulus_conductance_le_twelve r hr)).trans_eq
        (by norm_num)

end LocalLossBound

namespace LocalFullExpectation

/-- The full observable has the same real and nonnegative integral on its actual law.
Finiteness and integrability follow from full support, not a truncation premise. -/
theorem real_expectation_eq_lintegral (D : Finset (Site 2)) (P : OneSet D)
    (A : Set (Site 2)) (N : ℕ)
    (hD : (D : Set (Site 2)) ⊆ (boxSites N : Set (Site 2))) :
    (∫ σ, (LocalFullContacts.full A σ).toReal
      ∂wilsonColorLaw (LocalZeroExterior.domainRoots D P)) =
    (∫⁻ σ, LocalFullContacts.full A σ
      ∂wilsonColorLaw (LocalZeroExterior.domainRoots D P)).toReal := by
  have hfinite : ∀ᵐ σ ∂wilsonColorLaw (LocalZeroExterior.domainRoots D P),
      LocalFullContacts.full A σ ≠ ⊤ := by
    filter_upwards [LocalFullContacts.ae_support D P] with σ hσ
    rw [LocalFullContacts.full_eq_window D A N hD σ hσ]
    exact ENNReal.natCast_ne_top _
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun _ => ENNReal.toReal_nonneg))
    (integrable_full D P A N hD).aestronglyMeasurable]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hfinite] with σ hσ
  exact ENNReal.ofReal_toReal hσ

/-- The real full unwanted-contact mean is at most twelve on the same source law. -/
theorem real_expectation_le_twelve (r : ℕ) (hr : 1 ≤ r)
    (D : Finset (Site 2)) (P : OneSet D) (A : Set (Site 2))
    (hDbox : (D : Set (Site 2)) ⊆ (boxSites (2*r-1) : Set (Site 2)))
    (hPbox : (P.val.image Subtype.val : Set (Site 2)) ⊆ (boxSites r : Set (Site 2)))
    (hExit : ∀ y ∈ D, ∀ x, x ∉ D → x ∉ A → (lattice 2).Adj y x →
      x ∉ boxSites (2*r-1)) :
    (∫ σ, (LocalFullContacts.full ((D : Set (Site 2))ᶜ \ A) σ).toReal
      ∂wilsonColorLaw (LocalZeroExterior.domainRoots D P)) ≤ 12 := by
  rw [real_expectation_eq_lintegral D P _ (2*r-1) hDbox]
  have hb := LocalLossBound.expectation_le_twelve r hr D P A hDbox hPbox hExit
  exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top (by norm_num) hb)
    (by norm_num)).mpr hb

end LocalFullExpectation

namespace LocalSourceLoss

/-- The actual stopped-path source network and full unwanted-contact mean twelve.
All domain, path, original marked-copy and annulus conditions are produced. -/
theorem exists_local_loss_bound_twelve (r : ℕ) (hr : 10^30 ≤ r) (R : RootPair)
    (_hcofinite : (R.zero ∪ R.one)ᶜ.Finite)
    (h0 : (0 : Site 2) ∈ R.zero)
    (hneigh : ∃ b ∈ R.one, (lattice 2).Adj 0 b)
    (hZero : ((lattice 2).induce R.zero).Connected)
    (hfar : ∃ x ∈ R.zero, 2*r ≤ siteRadius 0 x)
    (hOne : ((lattice 2).induce R.one).Connected)
    (hmeet : ∃ y ∈ R.one, siteRadius 0 y = r) :
    ∃ (D : Finset (Site 2)) (P : OneSet D)
      (_hD : ((lattice 2).induce (D : Set (Site 2))).Connected)
      (marked : MarkedCopy D P) (b y : Site 2) (q : (lattice 2).Walk b y),
      b ∈ R.one ∧ (lattice 2).Adj 0 b ∧
      ((lattice 2).induce (D : Set (Site 2))ᶜ).Connected ∧
      ((lattice 2).induce (P.val.image Subtype.val : Set (Site 2))).Connected ∧
      P.val.image Subtype.val = q.support.toFinset ∧ q.IsPath ∧ siteRadius 0 y = r ∧
      (∀ x ∈ q.support, x ∈ R.one ∧ x ∈ boxSites r) ∧
      (∀ x ∈ q.support, x ≠ y → siteRadius 0 x < r) ∧
      ((originalA marked.val = 0 ∧ originalB marked.val = b) ∨
        (originalA marked.val = b ∧ originalB marked.val = 0)) ∧
      b ∈ D ∧ (0 : Site 2) ∉ D ∧ R.zero ⊆ (D : Set (Site 2))ᶜ ∧
      (D : Set (Site 2)) ⊆ (boxSites (2*r-1) : Set (Site 2)) ∧
      (∃ hbU : b ∈ (boxSites (2*r-1)).filter (fun x => x ∉ R.zero),
        D = JointFiniteComponent.componentSites ((boxSites (2*r-1)).filter (fun x => x ∉ R.zero)) ⟨b,hbU⟩) ∧
      (∀ x ∈ D, ∀ z, z ∉ D → z ∉ R.zero → (lattice 2).Adj x z → z ∉ boxSites (2*r-1)) ∧
      (∀ᵐ σ ∂wilsonColorLaw (LocalZeroExterior.domainRoots D P),
        (∀ x ∉ D, σ x = false) ∧
        LocalFullContacts.full ((D : Set (Site 2))ᶜ \ R.zero) σ =
          (localContacts ((D : Set (Site 2))ᶜ \ R.zero) 0 (2*r) σ : ℝ≥0∞)) ∧
      Integrable (fun σ => (LocalFullContacts.full ((D : Set (Site 2))ᶜ \ R.zero) σ).toReal)
        (wilsonColorLaw (LocalZeroExterior.domainRoots D P)) ∧
      (∫⁻ σ, LocalFullContacts.full ((D : Set (Site 2))ᶜ \ R.zero) σ
        ∂wilsonColorLaw (LocalZeroExterior.domainRoots D P)) ≤ 12 ∧
      (∫ σ, (LocalFullContacts.full ((D : Set (Site 2))ᶜ \ R.zero) σ).toReal
        ∂wilsonColorLaw (LocalZeroExterior.domainRoots D P)) ≤ 12 := by
  obtain ⟨b, hb, hadj⟩ := hneigh
  obtain ⟨D, P, hD, marked, y, q, hDc, hPc, hPQ, hq, hy, hroots, hfirst, hmark,
    hbD, h0D, hA, hDB, _hm, _hupper, hExit⟩ :=
    LocalSourceNetwork.exists_network r hr R h0 b hb hadj hZero hfar hOne hmeet
  have hr1 : 1 ≤ r := (by norm_num : 1 ≤ 10^30).trans hr
  have hPB : (P.val.image Subtype.val : Set (Site 2)) ⊆ (boxSites r : Set (Site 2)) := by
    intro x hx
    rw [hPQ] at hx
    exact (hroots x (List.mem_toFinset.mp hx)).2
  refine ⟨D, P, hD, marked, b, y, q, hb, hadj, hDc, hPc, hPQ, hq, hy, hroots,
    hfirst, hmark, hbD, h0D, hA, hDB,
    LocalComponentIdentification.component_eq (2*r-1) R.zero b D hD hbD hDB hA hExit,
    hExit, ?_, LocalFullExpectation.integrable_full D P _ (2*r-1) hDB,
    LocalLossBound.expectation_le_twelve r hr1 D P R.zero hDB hPB hExit,
    LocalFullExpectation.real_expectation_le_twelve r hr1 D P R.zero hDB hPB hExit⟩
  filter_upwards [LocalFullContacts.ae_support D P] with σ hσ
  refine ⟨hσ, ?_⟩
  have hrad : 2*r-1+1 = 2*r := by omega
  simpa only [hrad] using
    LocalFullContacts.full_eq_window D ((D : Set (Site 2))ᶜ \ R.zero) (2*r-1) hDB σ hσ

end LocalSourceLoss

end
