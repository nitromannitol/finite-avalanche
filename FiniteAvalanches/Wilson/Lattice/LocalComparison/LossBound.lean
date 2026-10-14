import FiniteAvalanches.Wilson.Lattice.LocalComparison.AnnulusCopies
import FiniteAvalanches.Wilson.Lattice.LocalComparison.AnnulusHitting
import FiniteAvalanches.Wilson.Lattice.LocalComparison.ElectricalSymmetry

set_option autoImplicit false
namespace LocalLossBound
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteWired FiniteAvalanches.Needle FiniteAvalanches.RevealedRoots
open FiniteAvalanches.Wilson.Lattice MeasureTheory
open scoped Classical ENNReal
noncomputable section

/-- The literal active vertices of the inner square in the annulus. -/
def inner (r : ℕ) : Finset (Active (2*r-1)) :=
  Finset.univ.filter (fun x => siteRadius 0 (site x) ≤ r)

theorem inner_image (r : ℕ) (hr : 1 ≤ r) : (inner r).image site = boxSites r := by
  ext x
  constructor
  · intro hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    apply (mem_box_sites _ _).mpr
    intro i
    simpa only [Pi.zero_apply,sub_zero,abs_le] using
      (siteRadius_le_iff 0 (site y) r).mp (Finset.mem_filter.mp hy).2 i
  · intro hx
    have hxi := (mem_box_sites r x).mp hx
    have hxN : inBox (2*r-1) x := by
      intro i
      have hi := hxi i
      constructor <;> omega
    refine Finset.mem_image.mpr ⟨activeOfSite (2*r-1) x hxN,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
    apply (siteRadius_le_iff 0 x r).mpr
    intro i
    simpa only [Pi.zero_apply,sub_zero,abs_le] using hxi i

theorem inner_nonempty (r : ℕ) (hr : 1 ≤ r) : (inner r).Nonempty := by
  have h0 : (0 : Site 2) ∈ boxSites r := (mem_box_sites _ _).mpr (by intro i; simp)
  rw [← inner_image r hr] at h0
  obtain ⟨x,hx,_⟩ := Finset.mem_image.mp h0
  exact ⟨x,hx⟩

/-- Exact import adapter for both already checked annulus voltage orientations. -/
theorem annulus_oriented_bounds (r : ℕ) (hr : 1 ≤ r) :
    wiredConductance (2*r-1) (inner r) ≤ 16 ∧
    (let f := fun v : Vertex (2*r-1) => 1-voltage (2*r-1) (inner r) v;
      f none = 0 ∧ (∀ x ∈ inner r, f (some x) = 1) ∧
      FiniteAvalanches.Electrical.energy
        (fun e : Edge (2*r-1) => (endpoints e).1) (fun e => (endpoints e).2) f ≤ 16) := by
  exact ⟨JointNeedleGeometry.annulus_sixteen r hr,JointElectricalSymmetry.local_annulus_trial r hr⟩

/-- The actual outer-origin hitting sum is the once-per-copy annulus conductance. -/
theorem annulus_hitting_sum (r : ℕ) (hr : 1 ≤ r) :
    (∑ x ∈ LocalAnnulusCopies.outerSites (2*r-1), ∑ y ∈ nbrFinset x,
      walkLaw (hitBefore (boxSites (2*r-1) : Set (Site 2))ᶜ (boxSites r) y)) =
        ENNReal.ofReal (wiredConductance (2*r-1) (inner r)) := by
  have he : (boxSites (2*r-1) : Set (Site 2)) = box 2 (2*r-1) := by
    ext x
    exact (mem_box_sites _ _).trans (inBox_iff _ _)
  rw [he,← inner_image r hr]
  simp_rw [LocalAnnulusHitting.reverse_hitting _ _ (inner_nonempty r hr)]
  simp_rw [← ENNReal.ofReal_sum_of_nonneg
    (fun y _ => LocalAnnulusCopies.reverse_potential_nonneg _ _ y)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ =>
    Finset.sum_nonneg (fun y _ => LocalAnnulusCopies.reverse_potential_nonneg _ _ y))]
  congr 1
  exact LocalAnnulusCopies.exterior_sum_eq_conductance _ _

/-- The hitting-sum dictionary also holds over every original exterior lattice origin. -/
theorem full_annulus_hitting_sum (r : ℕ) (hr : 1 ≤ r) :
    (∑' x : Site 2, if x ∉ boxSites (2*r-1) then ∑ y ∈ nbrFinset x,
      walkLaw (hitBefore (boxSites (2*r-1) : Set (Site 2))ᶜ (boxSites r) y) else 0) =
        ENNReal.ofReal (wiredConductance (2*r-1) (inner r)) := by
  let O := LocalAnnulusCopies.outerSites (2*r-1)
  have he : (boxSites (2*r-1) : Set (Site 2)) = box 2 (2*r-1) := by
    ext x
    exact (mem_box_sites _ _).trans (inBox_iff _ _)
  have hyzero (y : Site 2) (hy : y ∉ boxSites (2*r-1)) :
      walkLaw (hitBefore (boxSites (2*r-1) : Set (Site 2))ᶜ (boxSites r) y) = 0 := by
    rw [he,← inner_image r hr,LocalAnnulusHitting.reverse_hitting _ _ (inner_nonempty r hr),
      potential_exterior _ _ y (fun hm => hy ((mem_box_sites _ _).mpr ((inBox_iff _ _).mpr hm))),
      sub_self,ENNReal.ofReal_zero]
  rw [tsum_eq_sum (s := O) (by
    intro x hx
    by_cases hxB : x ∈ boxSites (2*r-1)
    · rw [if_neg (not_not.mpr hxB)]
    · rw [if_pos hxB]
      apply Finset.sum_eq_zero
      intro y hy
      apply hyzero
      intro hyB
      exact hx (Finset.mem_filter.mpr ⟨LocalFullContacts.neighbor_box (2*r-1) x y hyB hy,hxB⟩))]
  calc
    _ = ∑ x ∈ O, ∑ y ∈ nbrFinset x,
        walkLaw (hitBefore (boxSites (2*r-1) : Set (Site 2))ᶜ (boxSites r) y) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [if_pos (Finset.mem_filter.mp hx).2]
    _ = _ := annulus_hitting_sum r hr

/-- The exact B_(2r) window for the full unwanted observable. -/
def unwantedWindow (r : ℕ) (D : Finset (Site 2)) (A : Set (Site 2)) : Finset (Site 2) :=
  (window 0 (2*r)).filter (fun x => x ∈ (D : Set (Site 2))ᶜ \ A)

theorem full_expectation_eq_hitting (r : ℕ) (hr : 1 ≤ r)
    (D : Finset (Site 2)) (P : FiniteAvalanches.Electrical.Plane.SourceLattice.OneSet D)
    (A : Set (Site 2))
    (hDbox : (D : Set (Site 2)) ⊆ (boxSites (2*r-1) : Set (Site 2))) :
    (∫⁻ σ, LocalFullContacts.full ((D : Set (Site 2))ᶜ \ A) σ
      ∂wilsonColorLaw (LocalZeroExterior.domainRoots D P)) =
    ∑ x ∈ unwantedWindow r D A, ∑ y ∈ nbrFinset x,
      walkLaw (hitBefore (LocalZeroExterior.domainRoots D P).zero (LocalZeroExterior.domainRoots D P).one y) := by
  have hrad : 2*r-1+1 = 2*r := by omega
  have hFull : (fun σ => LocalFullContacts.full ((D : Set (Site 2))ᶜ \ A) σ) =ᵐ[wilsonColorLaw (LocalZeroExterior.domainRoots D P)]
      (fun σ => (contacts (unwantedWindow r D A) σ : ℝ≥0∞)) := by
    filter_upwards [LocalFullContacts.ae_support D P] with σ hσ
    have hw : localContacts ((D : Set (Site 2))ᶜ \ A) 0 (2*r-1+1) σ =
        contacts (unwantedWindow r D A) σ := by
      unfold localContacts
      congr 1
      ext x
      simp only [unwantedWindow,Finset.mem_filter,hrad]
    exact (LocalFullContacts.full_eq_window D ((D : Set (Site 2))ᶜ \ A)
      (2*r-1) hDbox σ hσ).trans (congrArg (fun n : ℕ => (n : ℝ≥0∞)) hw)
  calc
    _ = ∫⁻ σ, (contacts (unwantedWindow r D A) σ : ℝ≥0∞)
        ∂wilsonColorLaw (LocalZeroExterior.domainRoots D P) := lintegral_congr_ae hFull
    _ = _ := by
      simp_rw [LocalFullContacts.cast_contacts]
      exact contact_expectation_eq_hitting (LocalZeroExterior.domainRoots D P) (unwantedWindow r D A)

theorem unwanted_sum_zero_off_annulus (r : ℕ)
    (D : Finset (Site 2)) (P : FiniteAvalanches.Electrical.Plane.SourceLattice.OneSet D)
    (A : Set (Site 2))
    (hDbox : (D : Set (Site 2)) ⊆ (boxSites (2*r-1) : Set (Site 2)))
    (hExit : ∀ y ∈ D, ∀ x, x ∉ D → x ∉ A → (lattice 2).Adj y x → x ∉ boxSites (2*r-1))
    (x : Site 2) (hx : x ∈ unwantedWindow r D A)
    (hxO : x ∉ LocalAnnulusCopies.outerSites (2*r-1)) :
    (∑ y ∈ nbrFinset x, walkLaw (hitBefore (LocalZeroExterior.domainRoots D P).zero
      (LocalZeroExterior.domainRoots D P).one y)) = 0 := by
  apply Finset.sum_eq_zero
  intro y hy
  have hyD : y ∉ D := by
    intro hyD
    have hxA : x ∈ (D : Set (Site 2))ᶜ \ A := (Finset.mem_filter.mp hx).2
    have hxN := LocalFullContacts.neighbor_box (2*r-1) x y (hDbox hyD) hy
    exact hxO (Finset.mem_filter.mpr ⟨hxN,hExit y hyD x hxA.1 hxA.2
      ((mem_neighbors_iff x y).mp hy).symm⟩)
  rw [hitBefore_of_zero_root (LocalZeroExterior.domainRoots D P) hyD,measure_empty]

theorem domain_hitting_le_annulus (r : ℕ)
    (D : Finset (Site 2)) (P : FiniteAvalanches.Electrical.Plane.SourceLattice.OneSet D)
    (hDbox : (D : Set (Site 2)) ⊆ (boxSites (2*r-1) : Set (Site 2)))
    (hPbox : (P.val.image Subtype.val : Set (Site 2)) ⊆ (boxSites r : Set (Site 2))) (y : Site 2) :
    walkLaw (hitBefore (LocalZeroExterior.domainRoots D P).zero (LocalZeroExterior.domainRoots D P).one y) ≤
      walkLaw (hitBefore (boxSites (2*r-1) : Set (Site 2))ᶜ (boxSites r) y) := by
  apply measure_mono
  apply LocalAnnulusHitting.hitting_mono
  · intro x hx hxD
    exact hx (hDbox hxD)
  · exact hPbox

                                                                   
                                                                                        
theorem expectation_le_sixteen (r : ℕ) (hr : 1 ≤ r)
    (D : Finset (Site 2)) (P : FiniteAvalanches.Electrical.Plane.SourceLattice.OneSet D)
    (A : Set (Site 2))
    (hDbox : (D : Set (Site 2)) ⊆ (boxSites (2*r-1) : Set (Site 2)))
    (hPbox : (P.val.image Subtype.val : Set (Site 2)) ⊆ (boxSites r : Set (Site 2)))
    (hExit : ∀ y ∈ D, ∀ x, x ∉ D → x ∉ A → (lattice 2).Adj y x → x ∉ boxSites (2*r-1)) :
    (∫⁻ σ, LocalFullContacts.full ((D : Set (Site 2))ᶜ \ A) σ
      ∂wilsonColorLaw (LocalZeroExterior.domainRoots D P)) ≤ 16 := by
  let K := unwantedWindow r D A
  let O := LocalAnnulusCopies.outerSites (2*r-1)
  let R := LocalZeroExterior.domainRoots D P
  rw [full_expectation_eq_hitting r hr D P A hDbox]
  calc
    _ = ∑ x ∈ K ∩ O, ∑ y ∈ nbrFinset x, walkLaw (hitBefore R.zero R.one y) := by
      apply (Finset.sum_subset Finset.inter_subset_left ?_).symm
      intro x hx hxKO
      exact unwanted_sum_zero_off_annulus r D P A hDbox hExit x hx
        (fun hxO => hxKO (Finset.mem_inter.mpr ⟨hx,hxO⟩))
    _ ≤ ∑ x ∈ K ∩ O, ∑ y ∈ nbrFinset x,
        walkLaw (hitBefore (boxSites (2*r-1) : Set (Site 2))ᶜ (boxSites r) y) :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ =>
        domain_hitting_le_annulus r D P hDbox hPbox y))
    _ ≤ ∑ x ∈ O, ∑ y ∈ nbrFinset x,
        walkLaw (hitBefore (boxSites (2*r-1) : Set (Site 2))ᶜ (boxSites r) y) :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun _ _ _ => bot_le)
    _ = ENNReal.ofReal (wiredConductance (2*r-1) (inner r)) := annulus_hitting_sum r hr
    _ ≤ 16 := by
      exact (ENNReal.ofReal_le_ofReal (annulus_oriented_bounds r hr).1).trans_eq (by norm_num)

end
end LocalLossBound
