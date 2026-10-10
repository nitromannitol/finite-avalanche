import FiniteAvalanches.Wilson.Lattice.LocalComparison.MomentLaw
import FiniteAvalanches.Wilson.Lattice.LocalComparison.SourceBounds
import FiniteAvalanches.Wilson.Lattice.LocalComparison.ReferenceNumeric

set_option autoImplicit false
namespace LocalReferenceStepTwo
open LatticeProb FiniteAvalanches FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Sandpile FiniteAvalanches.Electrical
open FiniteAvalanches.Electrical.Plane.SourceLattice MeasureTheory
open scoped Classical BigOperators
noncomputable section

/-- Actual local Step 2, conditional only on the entire current reference proposition. -/
theorem conditional_local_second_moment
    (hReference :

    ∃ C : ℝ, ∀ (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (_hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (_hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P),
    let a := copyA D P marked
    let b := copyB D P marked
    let J := StatementTypes.graph D P marked
    let F := J.RootedForest ({alpha D P, beta D P} : Set (Vertex D P))
    letI : Nonempty F := Repair8.forest_nonempty D P hD marked
    let phi := Repair8.voltage D P hD marked
    let Y : F → ℝ := fun f => ∑ z : Plane.Dart (Copy D P marked),
      if Plane.tail a b z = alpha D P ∧ J.reaches f.val (Plane.head a b z) (beta D P)
      then 1 else 0
    let mean := (∑ f : F, Y f)/(Fintype.card F : ℝ)
    let variance := (∑ f : F, (Y f-mean)^2)/(Fintype.card F : ℝ)
    let M := energy a b phi
    let m := ((domainCopies D).filter fun e =>
      (originalA e ∈ D ∧ originalB e ∉ D) ∨ (originalB e ∈ D ∧ originalA e ∉ D)).card-1
    mean = M ∧ variance ≤ C*mean*(1+Real.log ((m : ℝ) / mean))
    ) :
    ∃ Cpositive : ℝ, 1 ≤ Cpositive ∧ 0 ≤ 1+8*Cpositive ∧
    ∀ (r : ℕ) (_hr : 10^30 ≤ r) (R : RootPair)
      (_hcofinite : (R.zero ∪ R.one)ᶜ.Finite)
      (_h0 : (0 : Site 2) ∈ R.zero)
      (_hneigh : ∃ b ∈ R.one, (lattice 2).Adj 0 b)
      (_hZero : ((lattice 2).induce R.zero).Connected)
      (_hfar : ∃ x ∈ R.zero, 2*r ≤ siteRadius 0 x)
      (_hOne : ((lattice 2).induce R.one).Connected)
      (_hmeet : ∃ y ∈ R.one, siteRadius 0 y = r),
    ∃ (D : Finset (Site 2)) (P : OneSet D)
      (hD : ((lattice 2).induce (D : Set (Site 2))).Connected)
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
      (∀ x ∈ D, ∀ z, z ∉ D → z ∉ R.zero → (lattice 2).Adj x z → z ∉ boxSites (2*r-1)) ∧
      (let μ := wilsonColorLaw (LocalZeroExterior.domainRoots D P)
       let Y := LocalMomentLaw.sourceY D
       let mean := ∫ σ, Y σ ∂μ
       let m := (latticeExits D).card-1
       (Set.range (LocalBoxContraction.referenceField D P marked)).Finite ∧
       (∀ σ, 0 < μ {σ} ↔ σ ∈ Set.range (LocalBoxContraction.referenceField D P marked)) ∧
       (∀ᵐ σ ∂μ, σ ∈ Set.range (LocalBoxContraction.referenceField D P marked)) ∧
       (∀ᵐ σ ∂μ, (∀ x ∉ D, σ x = false) ∧ 0 ≤ Y σ) ∧
       Integrable Y μ ∧ Integrable (fun σ => (Y σ)^2) μ ∧
       mean = energy (copyA D P marked) (copyB D P marked) (Repair8.voltage D P hD marked) ∧
       Real.log (r : ℝ)/2 ≤ mean ∧ 32 ≤ Real.log (r : ℝ)/2 ∧ 32 ≤ mean ∧
       mean ≤ (m : ℝ) ∧ m ≤ r^3 ∧
       (∫ σ, (Y σ)^2 ∂μ) ≤ (1+8*Cpositive)*mean^2) := by
  obtain ⟨C,hC⟩ := hReference
  have hCp : 0 ≤ max 1 C := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 C)
  refine ⟨max 1 C, le_max_left 1 C, by positivity, ?_⟩
  intro r hr R hcofinite h0 hneigh hZero hfar hOne hmeet
  obtain ⟨D,P,hD,marked,b,y,q,hb,hadj,hDc,hP,hPQ,hq,hy,hqroots,hqfirst,hmark,
    hbD,h0D,hZD,hDB,_hlower,hbounds,hexit⟩ :=
    LocalSourceBounds.exists_bounded_network r hr R hcofinite h0 hneigh hZero hfar hOne hmeet
  refine ⟨D,P,hD,marked,b,y,q,hb,hadj,hDc,hP,hPQ,hq,hy,hqroots,hqfirst,hmark,
    hbD,h0D,hZD,hDB,hexit,?_⟩
  dsimp only at hbounds ⊢
  letI : Nonempty (ReferenceMoment.Forest D P marked) := Repair8.forest_nonempty D P hD marked
  have hmom := hC D P hD hDc hP marked
  dsimp only at hmom
  have hmean :
      (∑ f : ReferenceMoment.Forest D P marked, ReferenceMoment.boundaryContacts D P marked f)/
        (Fintype.card (ReferenceMoment.Forest D P marked) : ℝ) =
      energy (copyA D P marked) (copyB D P marked) (Repair8.voltage D P hD marked) := hmom.1
  have hvar := hmom.2
  change (∑ f : ReferenceMoment.Forest D P marked,
      (ReferenceMoment.boundaryContacts D P marked f -
        (∑ g : ReferenceMoment.Forest D P marked, ReferenceMoment.boundaryContacts D P marked g)/
          (Fintype.card (ReferenceMoment.Forest D P marked) : ℝ))^2)/
        (Fintype.card (ReferenceMoment.Forest D P marked) : ℝ) ≤
      C*((∑ g : ReferenceMoment.Forest D P marked, ReferenceMoment.boundaryContacts D P marked g)/
          (Fintype.card (ReferenceMoment.Forest D P marked) : ℝ))*
        (1+Real.log (((latticeExits D).card-1 : ℕ) /
          ((∑ g : ReferenceMoment.Forest D P marked, ReferenceMoment.boundaryContacts D P marked g)/
            (Fintype.card (ReferenceMoment.Forest D P marked) : ℝ)))) at hvar
  rw [hmean] at hvar
  have h32 := LocalEnergyNumeric.thirty_two_le_log_half r hr
  have hlog : 1 ≤ Real.log (r : ℝ) := by linarith only [h32]
  have hlogM : Real.log (r : ℝ) ≤ 2*energy (copyA D P marked) (copyB D P marked)
      (Repair8.voltage D P hD marked) := by linarith only [hbounds.1]
  have hmr : (((latticeExits D).card-1 : ℕ) : ℝ) ≤ (r : ℝ)^3 := by
    exact_mod_cast hbounds.2.2.2
  have hv := JointReferenceNumeric.variance_le_eight_sq C _ _ (r : ℝ) _
    hbounds.2.1 hlog hlogM hbounds.2.2.1 hmr hvar
  have hmax : max 0 C ≤ max 1 C := max_le_max_right C (by norm_num)
  have hv' := hv.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmax (by norm_num : (0 : ℝ) ≤ 8)) (sq_nonneg _))
  have hsecond := JointFiniteProbability.second_moment_eq_variance_add_sq
    (ReferenceMoment.boundaryContacts D P marked)
  rw [hmean] at hsecond
  have hfiniteSecond :
      (∑ f : ReferenceMoment.Forest D P marked, (ReferenceMoment.boundaryContacts D P marked f)^2)/
        (Fintype.card (ReferenceMoment.Forest D P marked) : ℝ) ≤
      (1+8*max 1 C)*(energy (copyA D P marked) (copyB D P marked)
        (Repair8.voltage D P hD marked))^2 := by
    rw [hsecond]
    nlinarith only [hv']
  have hDbox : ∀ x ∈ D, FiniteWired.inBox (2*r-1) x :=
    fun x hx => (mem_box_sites _ _).mp (hDB hx)
  obtain ⟨hs,hfull,hsupport,hnonneg,hint,hint2,hmeanLaw,hsecondLaw⟩ :=
    LocalMomentLaw.actual_law_moments D P (2*r-1) hDbox marked
  have hmeanEnergy := hmeanLaw.trans hmean
  refine ⟨hs,hfull,hsupport,hnonneg,hint,hint2,hmeanEnergy,?_,h32,?_,?_,hbounds.2.2.2,?_⟩
  · rw [hmeanEnergy]; exact hbounds.1
  · rw [hmeanEnergy]; exact hbounds.2.1
  · rw [hmeanEnergy]; exact hbounds.2.2.1
  · rw [hsecondLaw,hmeanEnergy]
    exact hfiniteSecond

end
end LocalReferenceStepTwo
