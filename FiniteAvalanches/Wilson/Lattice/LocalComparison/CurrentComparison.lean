import FiniteAvalanches.Wilson.Lattice.LocalComparison.ReferenceMomentBound
import FiniteAvalanches.Wilson.Lattice.LocalComparison.ContactSupport
import FiniteAvalanches.Wilson.Lattice.LocalComparison.LossTwelve
import FiniteAvalanches.Wilson.Lattice.LocalComparison.EnergyUpper
import FiniteAvalanches.Wilson.Lattice.LocalComparison.CopiedEnergy
import FiniteAvalanches.Wilson.Lattice.LocalComparison.CurrentContactOrder

set_option autoImplicit false
namespace CurrentLocalComparison
open LatticeProb FiniteAvalanches FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Sandpile FiniteAvalanches.Electrical
open FiniteAvalanches.Electrical.Plane.SourceLattice MeasureTheory
open scoped Classical BigOperators ENNReal
noncomputable section

/-- The local comparison derived from the full reference moment statement. -/
theorem conditional_local_comparison
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
    ∃ ε : ℝ, 0 < ε ∧ ∀ (r : ℕ) (_hr : 10^30 ≤ r) (R : RootPair)
      (_hcofinite : (R.zero ∪ R.one)ᶜ.Finite)
      (_h0 : (0 : Site 2) ∈ R.zero)
      (_hneigh : ∃ b ∈ R.one, (lattice 2).Adj 0 b)
      (_hZero : ((lattice 2).induce R.zero).Connected)
      (_hfar : ∃ x ∈ R.zero, 2*r ≤ siteRadius 0 x)
      (_hOne : ((lattice 2).induce R.one).Connected)
      (_hmeet : ∃ y ∈ R.one, siteRadius 0 y = r),
      ε ≤ (wilsonColorLaw R).real
        (localContactEvent R.zero 0 (2*r) (Real.log (r : ℝ)/8)) := by
  obtain ⟨C,hC⟩ := hReference
  have hCp : 0 ≤ max 1 C := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 C)
  have hB : 0 < 1+8*max 1 C := by positivity
  refine ⟨1/(16*(1+8*max 1 C)), by positivity, ?_⟩
  intro r hr R hcofinite h0 hneigh hZero hfar hOne hmeet
  obtain ⟨D,P,hD,marked,b,y,q,_hb,hadj,hDc,hP,hPQ,_hq,hy,hqroots,_hqfirst,hmark,
    _hbD,h0D,hZD,hDB,_hcomponent,_hexit,_hsupportloss,_hintloss,_hlinloss,hlossfull⟩ :=
    LocalSourceLoss.exists_local_loss_bound_twelve r hr R hcofinite h0 hneigh hZero hfar hOne hmeet
  have hr1 : 1 ≤ r := (by norm_num : 1 ≤ 10^30).trans hr
  have hr100 : 100 ≤ r := (by norm_num : 100 ≤ 10^30).trans hr
  letI : Nonempty (ReferenceMoment.Forest D P marked) := Repair8.forest_nonempty D P hD marked
  let Y := ReferenceMoment.boundaryContacts D P marked
  let M := energy (copyA D P marked) (copyB D P marked) (Repair8.voltage D P hD marked)
  let X : ReferenceMoment.Forest D P marked → ℝ := fun f =>
    (LocalBoxContraction.exteriorContacts D R.zero (LocalBoxContraction.referenceField D P marked f) : ℝ)-1
  let Z : ReferenceMoment.Forest D P marked → ℝ := fun f =>
    (LocalBoxContraction.exteriorContacts D ((D : Set (Site 2))ᶜ \ R.zero)
      (LocalBoxContraction.referenceField D P marked f) : ℝ)
  have hphi := Repair8.voltage_spec D P hD marked
  have hlow : Real.log (r : ℝ)/2 ≤ M :=
    (LocalEnergyNumeric.log_half_le_harmonic_half r).trans
      (LocalCopiedEnergy.admissible_energy_lower r R h0 hZero hfar b y hadj q hy D P hZD hPQ
        marked hmark (Repair8.voltage D P hD marked) hphi.1 hphi.2.1)
  have h32log := LocalEnergyNumeric.thirty_two_le_log_half r hr
  have h32 : 32 ≤ M := h32log.trans hlow
  have hMp : 0 < M := by linarith only [h32]
  have hMm : M ≤ (((latticeExits D).card-1 : ℕ) : ℝ) :=
    LocalEnergyUpper.voltage_energy_le_original_exits D P hD marked
  have hmr : (((latticeExits D).card-1 : ℕ) : ℝ) ≤ (r : ℝ)^3 := by
    exact_mod_cast JointBoundarySize.reference_boundary_le_cube r hr100 D hDB
  have hmom := hC D P hD hDc hP marked
  dsimp only at hmom
  have hmean : (∑ f, Y f)/(Fintype.card (ReferenceMoment.Forest D P marked) : ℝ) = M := hmom.1
  have hvar := hmom.2
  change (∑ f, (Y f - (∑ g, Y g)/(Fintype.card (ReferenceMoment.Forest D P marked) : ℝ))^2)/
      (Fintype.card (ReferenceMoment.Forest D P marked) : ℝ) ≤
    C*((∑ g, Y g)/(Fintype.card (ReferenceMoment.Forest D P marked) : ℝ))*
      (1+Real.log ((((latticeExits D).card-1 : ℕ) : ℝ) /
        ((∑ g, Y g)/(Fintype.card (ReferenceMoment.Forest D P marked) : ℝ)))) at hvar
  rw [hmean] at hvar
  have hv := JointReferenceNumeric.variance_le_eight_sq C M _ (r : ℝ) _ h32
    (by linarith only [h32log]) (by linarith only [hlow]) hMm hmr hvar
  have hmax : max 0 C ≤ max 1 C := max_le_max_right C (by norm_num)
  have hv' := hv.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmax (by norm_num : (0 : ℝ) ≤ 8)) (sq_nonneg M))
  have hsecond := JointFiniteProbability.second_moment_eq_variance_add_sq Y
  rw [hmean] at hsecond
  have hsecondY : (∑ f, (Y f)^2)/(Fintype.card (ReferenceMoment.Forest D P marked) : ℝ) ≤
      (1+8*max 1 C)*M^2 := by
    rw [hsecond]
    nlinarith only [hv']
  have hDbox : ∀ x ∈ D, FiniteWired.inBox (2*r-1) x :=
    fun x hx => (mem_box_sites _ _).mp (hDB hx)
  have hlaw := LocalBoxContraction.reference_color_law D P (2*r-1) hDbox marked
  have hfield := measurable_of_finite (LocalBoxContraction.referenceField D P marked)
  have hlossEq :
      (∫ σ, (LocalFullContacts.full ((D : Set (Site 2))ᶜ \ R.zero) σ).toReal
        ∂wilsonColorLaw (LocalZeroExterior.domainRoots D P)) =
      (∑ f, Z f)/(Fintype.card (ReferenceMoment.Forest D P marked) : ℝ) := by
    rw [← hlaw, integral_map
      (f := fun σ : ColorField => (LocalFullContacts.full ((D : Set (Site 2))ᶜ \ R.zero) σ).toReal)
      hfield.aemeasurable
      (ENNReal.measurable_toReal.comp (LocalFullContacts.measurable_full ((D : Set (Site 2))ᶜ \ R.zero))).aestronglyMeasurable,
      integral_uniformMeasure, Nat.card_eq_fintype_card]
    congr 1
    apply Finset.sum_congr rfl
    intro f _
    rw [LocalContactSupport.full_eq_exterior D _ (fun _ hx => hx.1) _
      (LocalBoxContraction.reference_field_exterior D P marked f), ENNReal.toReal_natCast]
  rw [hlossEq] at hlossfull
  have hbP : b ∈ P.val.image Subtype.val := by
    rw [hPQ]
    exact List.mem_toFinset.mpr q.start_mem_support
  have hX0 (f : ReferenceMoment.Forest D P marked) : 0 ≤ X f := by
    have h := LocalContactSupport.exterior_at_least_one D P marked f R.zero h0 h0D b hbP hadj
    have hh : (1 : ℝ) ≤ LocalBoxContraction.exteriorContacts D R.zero
        (LocalBoxContraction.referenceField D P marked f) := by exact_mod_cast h
    exact sub_nonneg.mpr hh
  have hZ0 (f : ReferenceMoment.Forest D P marked) : 0 ≤ Z f := Nat.cast_nonneg _
  have hid (f : ReferenceMoment.Forest D P marked) : Y f = X f + Z f :=
    LocalBoxContraction.source_observable_identity D P marked f R.zero
  have hXle (f : ReferenceMoment.Forest D P marked) : X f ≤ Y f := by
    rw [hid]
    exact le_add_of_nonneg_right (hZ0 f)
  have hsplit :
      (∑ f, X f)/(Fintype.card (ReferenceMoment.Forest D P marked) : ℝ) +
      (∑ f, Z f)/(Fintype.card (ReferenceMoment.Forest D P marked) : ℝ) = M := by
    rw [← add_div, ← Finset.sum_add_distrib, ← hmean]
    congr 1
    apply Finset.sum_congr rfl
    intro f _
    exact (hid f).symm
  have hmeanX : M/2 ≤ (∑ f, X f)/(Fintype.card (ReferenceMoment.Forest D P marked) : ℝ) := by
    linarith only [hsplit,hlossfull,h32]
  have hsecondX : (∑ f, (X f)^2)/(Fintype.card (ReferenceMoment.Forest D P marked) : ℝ) ≤
      (1+8*max 1 C)*M^2 := by
    apply le_trans _ hsecondY
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact Finset.sum_le_sum (fun f _ => (sq_le_sq₀ (hX0 f) (LocalMomentLaw.reference_nonneg D P marked f)).mpr (hXle f))
  have hpz := JointFiniteProbability.paley_zygmund_quarter X M (1+8*max 1 C)
    hMp hB hX0 hmeanX hsecondX
  have hpzMeasure : 1/(16*(1+8*max 1 C)) ≤
      (uniformMeasure (ReferenceMoment.Forest D P marked)).real {f | M/4 ≤ X f} := by
    rw [uniformMeasure_real_apply, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
    exact hpz
  have hlocal : 1/(16*(1+8*max 1 C)) ≤
      (wilsonColorLaw (LocalZeroExterior.domainRoots D P)).real
        (localContactEvent R.zero 0 (2*r) (Real.log (r : ℝ)/8)) := by
    apply hpzMeasure.trans
    rw [← hlaw]
    simp only [Measure.real]
    rw [Measure.map_apply hfield (isClopen_localContactEvent _ _ _ _).isClosed.measurableSet]
    change (uniformMeasure (ReferenceMoment.Forest D P marked)).real {f | M/4 ≤ X f} ≤ _
    apply measureReal_mono ?_ (by finiteness)
    intro f hf
    change M/4 ≤ X f at hf
    change Real.log (r : ℝ)/8 ≤
      (localContacts R.zero 0 (2*r) (LocalBoxContraction.referenceField D P marked f) : ℝ)
    rw [← LocalContactSupport.exterior_eq_window r hr1 D hDB R.zero hZD _
      (LocalBoxContraction.reference_field_exterior D P marked f)]
    have hxf : (LocalBoxContraction.exteriorContacts D R.zero
      (LocalBoxContraction.referenceField D P marked f) : ℝ) = X f + 1 := by dsimp only [X]; ring
    rw [hxf]
    linarith only [hf,hlow]
  have hQco : ((LocalZeroExterior.domainRoots D P).zero ∪
      (LocalZeroExterior.domainRoots D P).one)ᶜ.Finite := by
    apply D.finite_toSet.subset
    intro x hx
    by_contra hxD
    exact hx (Or.inl hxD)
  have hPone : (LocalZeroExterior.domainRoots D P).one ⊆ R.one := by
    intro x hx
    change x ∈ P.val.image Subtype.val at hx
    rw [hPQ] at hx
    exact (hqroots x (List.mem_toFinset.mp hx)).1
  exact hlocal.trans (JointCurrentContactOrder.local_event_mono_cofinite R
    (LocalZeroExterior.domainRoots D P) hcofinite hQco hZD hPone R.zero 0 (2*r) (Real.log (r : ℝ)/8))

end
end CurrentLocalComparison
