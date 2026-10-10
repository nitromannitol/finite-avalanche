import FiniteAvalanches.Wilson.Lattice.RevealedRoots.AddedLoss
import FiniteAvalanches.Wilson.Lattice.RevealedRoots.GeometryAssembly
import FiniteAvalanches.Wilson.Lattice.LocalComparison.ScaleGeometry
import FiniteAvalanches.Wilson.Lattice.TranslationColorLaw

set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.Revealed19
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory
open scoped Classical BigOperators ENNReal
noncomputable section

/-- Exact transport of the whole local event under the actual Wilson color law. -/
theorem local_probability_translate (R : RootPair) (w : Site 2) (r : ℕ) (t : ℝ) :
    (wilsonColorLaw (Translation.roots R (-w))).real
      (localContactEvent (Translation.roots R (-w)).zero 0 r t) =
    (wilsonColorLaw R).real (localContactEvent R.zero w r t) := by
  simp only [Measure.real]
  rw [← Translation.wilsonColorLaw_map,
    Measure.map_apply (Translation.measurable_colors (-w))
      (isClopen_localContactEvent _ _ _ _).isClosed.measurableSet]
  congr 1
  congr 1
  ext σ
  change (t ≤ (localContacts (Translation.roots R (-w)).zero 0 r
    (Translation.colors (-w) σ) : ℝ)) ↔ t ≤ (localContacts R.zero w r σ : ℝ)
  rw [JointTranslatedGeometry.local_contacts_shift]

/-- Actual finite full-contact integrability supplies Markov; the paid scale is produced later. -/
theorem added_markov (R : RootPair) (K Z : Finset (Site 2)) (t p : ℝ) (ht : 0 < t)
    (hmean : (∫ σ, (contacts (Z \ K) σ : ℝ) ∂wilsonColorLaw R) ≤ p*t) :
    (wilsonColorLaw R).real {σ | t < (contacts (Z \ K) σ : ℝ)} ≤ p := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (wilsonColorLaw R) (fun _ => Nat.cast_nonneg (contacts (Z \ K) _)))
    (LocalFullExpectation.integrable_contacts R (Z \ K)) t
  have hp : (wilsonColorLaw R).real {σ | t < (contacts (Z \ K) σ : ℝ)} ≤
      (wilsonColorLaw R).real {σ | t ≤ (contacts (Z \ K) σ : ℝ)} :=
    measureReal_mono (by
      intro σ hx
      change t < (contacts (Z \ K) σ : ℝ) at hx
      exact hx.le) (by finiteness)
  have hb := (mul_le_mul_of_nonneg_left hp ht.le).trans (hm.trans hmean)
  exact (mul_le_mul_iff_right₀ ht).mp (by simpa only [mul_comm] using hb)

theorem local_finite_contacts (K : Finset (Site 2)) (w : Site 2) (r : ℕ) (σ : ColorField) :
    localContacts (K : Set (Site 2)) w r σ = contacts ((window w r) ∩ K) σ := by
  unfold localContacts
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_coe]

/-- Subtraction retains the full added-root loss, with all copied incidences. -/
theorem local_subtract_added (R : RootPair) (K Z : Finset (Site 2))
    (hR : R.zero = ((K ∪ Z : Finset (Site 2)) : Set (Site 2)))
    (w : Site 2) (r : ℕ) (t ε : ℝ)
    (hlocal : ε ≤ (wilsonColorLaw R).real (localContactEvent R.zero w r (2*t)))
    (hbad : (wilsonColorLaw R).real {σ | t < (contacts (Z \ K) σ : ℝ)} ≤ ε/2) :
    ε/2 ≤ (wilsonColorLaw R).real (localContactEvent (K : Set (Site 2)) w r t) := by
  let E := localContactEvent R.zero w r (2*t)
  let B := {σ : ColorField | t < (contacts (Z \ K) σ : ℝ)}
  have hsplit (σ : ColorField) : localContacts R.zero w r σ ≤
      localContacts (K : Set (Site 2)) w r σ + contacts (Z \ K) σ := by
    let F := (window w r).filter (fun x => x ∈ R.zero)
    have hF : F ⊆ K ∪ Z := by
      intro x hx
      have hxR := (Finset.mem_filter.mp hx).2
      rw [hR] at hxR
      exact hxR
    have hs := JointContactOrder.contacts_union_le K Z F hF σ
    rw [local_finite_contacts]
    unfold localContacts
    apply hs.trans
    apply Nat.add_le_add_right
    apply JointContactOrder.contacts_subset
    intro x hx
    exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_inter.mp hx).1).1,
      (Finset.mem_inter.mp hx).2⟩
  have hEB : E \ B ⊆ localContactEvent (K : Set (Site 2)) w r t := by
    intro σ hσ
    have he : 2*t ≤ (localContacts R.zero w r σ : ℝ) := hσ.1
    have hb : (contacts (Z \ K) σ : ℝ) ≤ t := le_of_not_gt hσ.2
    have hs : (localContacts R.zero w r σ : ℝ) ≤
        (localContacts (K : Set (Site 2)) w r σ : ℝ) + (contacts (Z \ K) σ : ℝ) := by
      exact_mod_cast hsplit σ
    change t ≤ (localContacts (K : Set (Site 2)) w r σ : ℝ)
    linarith only [he,hb,hs]
  have hu := le_measureReal_sdiff (μ := wilsonColorLaw R) (s₁ := E) (s₂ := B)
  have hsub : ε/2 ≤ (wilsonColorLaw R).real (E \ B) := by
    linarith only [hlocal,hbad,hu]
  exact hsub.trans (measureReal_mono hEB (by finiteness))

/-- The revealed half for a supplied closed local theorem and the same epsilon.
The helper's local input is discharged by the whole-reference joint assembly. -/
theorem revealed_of_local (ε : ℝ) (hε : 0 < ε)
    (hlocal : ∀ (r : ℕ), 10^30 ≤ r → ∀ R : RootPair,
      (R.zero ∪ R.one)ᶜ.Finite → 0 ∈ R.zero →
      (∃ b ∈ R.one, (lattice 2).Adj 0 b) →
      ((lattice 2).induce R.zero).Connected →
      (∃ x ∈ R.zero, 2*r ≤ siteRadius 0 x) →
      ((lattice 2).induce R.one).Connected →
      (∃ y ∈ R.one, siteRadius 0 y = r) →
      ε ≤ (wilsonColorLaw R).real
        (localContactEvent R.zero 0 (2*r) (Real.log (r : ℝ)/8))) :
    ∃ κ : ℕ, 30 ≤ κ ∧
      ∀ (K : Finset (Site 2)) (γ : Set (Site 2)),
        ((lattice 2).induce (K : Set (Site 2))).Connected →
        0 ∈ K → Disjoint (K : Set (Site 2)) γ →
        ((lattice 2).induce γ).Connected → γᶜ.Finite →
        (∃ b ∈ γ, (lattice 2).Adj 0 b) →
        ∀ h r : ℕ, 10 ≤ h → h^κ ≤ r →
        16*r ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) →
        ∀ R : RootPair, (K : Set (Site 2)) ⊆ R.zero →
          R.zero ⊆ (K : Set (Site 2)) ∪ (boxSites h : Set (Site 2)) →
          γ ⊆ R.one →
          ε/2 ≤ (wilsonColorLaw R).real
            (kContactEvent K (3*(r : ℝ)) (Real.log (r : ℝ)/16)) := by
  obtain ⟨κ,hκ,_hpaid,hscale⟩ := JointScaleGeometry.exists_uniform_kappa ε hε
  refine ⟨κ,hκ,?_⟩
  intro K γ hK h0 hd hγc hγf hn h r hh hr hdiam R hRK hRbox hRγ
  obtain ⟨w,Z,Q,hQ0,hZo,hRQ,hQR,hQout,hRcf,hQcf,
    hrscale,hwrle,hsf,hs0,hsn,hsc0,hsfar,hsc1,hsmeet,hbudget⟩ :=
    exists_revealed_roots κ hκ K γ hK h0 hd hγc hγf hn h r hh hr hdiam R hRK hRbox hRγ
  have hlocShift := hlocal r hrscale (Translation.roots Q (-w))
    hsf hs0 hsn hsc0 hsfar hsc1 hsmeet
  rw [local_probability_translate] at hlocShift
  obtain ⟨_hrscale,_htwo,_hlog,hpay⟩ := hscale h r hh hr
  obtain ⟨_hfinite,_hint,hmeanFull⟩ := added_mean_le_107 Q K Z h hQ0 hZo hQout hbudget
  have hmean : (∫ σ, (contacts (Z \ K) σ : ℝ) ∂wilsonColorLaw Q) ≤ 107*Real.log h := by
    have he := (added_full_finite_integrable Q K Z hQ0).1
    simpa only [he, ENNReal.toReal_natCast] using hmeanFull
  have hrpos : (1 : ℝ) < r := by
    exact_mod_cast (by omega : 1 < r)
  have ht : 0 < Real.log (r : ℝ)/16 := div_pos (Real.log_pos hrpos) (by norm_num)
  have hbad := added_markov Q K Z (Real.log (r : ℝ)/16) (ε/2) ht (hmean.trans hpay)
  have hloc : ε ≤ (wilsonColorLaw Q).real
      (localContactEvent Q.zero w (2*r) (2*(Real.log (r : ℝ)/16))) := by
    rw [show 2*(Real.log (r : ℝ)/16) = Real.log (r : ℝ)/8 by ring]
    exact hlocShift
  have hKloc := local_subtract_added Q K Z hQ0 w (2*r) (Real.log (r : ℝ)/16) ε hloc hbad
  have hbox : localContactEvent (K : Set (Site 2)) w (2*r) (Real.log (r : ℝ)/16) ⊆
      kContactEvent K (3*(r : ℝ)) (Real.log (r : ℝ)/16) := by
    intro σ hσ
    change Real.log (r : ℝ)/16 ≤ (localContacts (K : Set (Site 2)) w (2*r) σ : ℝ) at hσ
    change Real.log (r : ℝ)/16 ≤ (kContacts K (3*(r : ℝ)) σ : ℝ)
    exact hσ.trans (Nat.cast_le.mpr (JointScaleGeometry.shifted_contacts_le K w r hwrle σ))
  exact (hKloc.trans (measureReal_mono hbox (by finiteness))).trans
    (JointContactOrder.k_event_mono_cofinite R Q hRcf hQcf hRQ hQR K
      (3*(r : ℝ)) (Real.log (r : ℝ)/16))

end
end FiniteAvalanches.Wilson.Lattice.Revealed19
