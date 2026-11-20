import FiniteAvalanches.Support.Plane.CircleIntervalIsotopy

/-!
# The interval quotient and the additive circle

The quotient of the unit interval identifying its endpoints is homeomorphic to
the additive circle of period one.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

/-- The interval endpoint quotient is the standard additive circle. -/
noncomputable def circleQuotHomeomorph : CircleQuot ≃ₜ AddCircle (1 : ℝ) := by
  let A : Type := Icc (0 : ℝ) (0 + 1)
  let h : unitInterval ≃ₜ A := Homeomorph.setCongr (by simp [unitInterval])
  have hzero : h 0 = ⟨0, by norm_num⟩ := by apply Subtype.ext; rfl
  have hone : h 1 = ⟨1, by norm_num⟩ := by apply Subtype.ext; rfl
  have hrel (x y : unitInterval) : CircleEndpointIdent x y ↔
      AddCircle.EndpointIdent (1 : ℝ) 0 (h x) (h y) := by
    constructor
    · intro hxy
      cases hxy
      rw [hzero, hone]
      simpa only [zero_add] using
        (AddCircle.EndpointIdent.mk (p := (1 : ℝ)) (a := (0 : ℝ)))
    · intro hxy
      have hend : ∀ {a b : A}, AddCircle.EndpointIdent (1 : ℝ) 0 a b →
          a = ⟨0, by norm_num⟩ ∧ b = ⟨1, by norm_num⟩ := by
        intro a b hab
        cases hab
        refine ⟨rfl, ?_⟩
        apply Subtype.ext
        simp only [zero_add]
      obtain ⟨hx, hy⟩ := hend hxy
      have hx' : x = 0 := h.injective (hx.trans hzero.symm)
      have hy' : y = 1 := h.injective (hy.trans hone.symm)
      subst x
      subst y
      exact CircleEndpointIdent.mk
  let Q : CircleQuot ≃ Quot (AddCircle.EndpointIdent (1 : ℝ) 0) := Quot.congr h.toEquiv hrel
  have hQ : Continuous Q := by
    apply isQuotientMap_quot_mk.continuous_iff.mpr
    change Continuous (fun x : unitInterval => Quot.mk _ (h x))
    exact continuous_quot_mk.comp h.continuous
  have hQi : Continuous Q.symm := by
    apply isQuotientMap_quot_mk.continuous_iff.mpr
    change Continuous (fun x : A => Quot.mk _ (h.symm x))
    exact continuous_quot_mk.comp h.symm.continuous
  let R : CircleQuot ≃ₜ Quot (AddCircle.EndpointIdent (1 : ℝ) 0) :=
    ⟨Q, hQ, hQi⟩
  exact R.trans (AddCircle.homeoIccQuot (1 : ℝ) 0).symm

/-- A quotient point represented by `x` maps to the class of `x`. -/
theorem circleQuotHomeomorph_mk (x : unitInterval) :
    circleQuotHomeomorph (Quot.mk _ x) = ((x : ℝ) : AddCircle (1 : ℝ)) := by
  rfl

/-- An increasing interval homeomorphism induces an isotopy of the additive
circle, with jointly continuous inverses. -/
theorem exists_addCircle_isotopy_of_interval_homeomorph
    (f : unitInterval ≃ₜ unitInterval) (hf : StrictMono f) :
    ∃ E : unitInterval → AddCircle (1 : ℝ) ≃ AddCircle (1 : ℝ),
      Continuous (fun p : unitInterval × AddCircle (1 : ℝ) => E p.1 p.2) ∧
      Continuous (fun p : unitInterval × AddCircle (1 : ℝ) => (E p.1).symm p.2) ∧
      (∀ x, E 0 x = x) ∧
      (∀ x : unitInterval, E 1 ((x : ℝ) : AddCircle (1 : ℝ)) =
        (((f x : unitInterval) : ℝ) : AddCircle (1 : ℝ))) := by
  obtain ⟨E, hE, hEi, hE0, hE1⟩ := exists_circle_isotopy_of_interval_homeomorph f hf
  let H := circleQuotHomeomorph
  let G : unitInterval → AddCircle (1 : ℝ) ≃ AddCircle (1 : ℝ) :=
    fun t => H.symm.toEquiv.trans ((E t).trans H.toEquiv)
  have hG : Continuous (fun p : unitInterval × AddCircle (1 : ℝ) => G p.1 p.2) := by
    change Continuous (fun p : unitInterval × AddCircle (1 : ℝ) => H (E p.1 (H.symm p.2)))
    exact H.continuous.comp (hE.comp (continuous_fst.prodMk (H.symm.continuous.comp continuous_snd)))
  have hGi : Continuous (fun p : unitInterval × AddCircle (1 : ℝ) => (G p.1).symm p.2) := by
    change Continuous (fun p : unitInterval × AddCircle (1 : ℝ) => H ((E p.1).symm (H.symm p.2)))
    exact H.continuous.comp (hEi.comp (continuous_fst.prodMk (H.symm.continuous.comp continuous_snd)))
  refine ⟨G, hG, hGi, ?_, ?_⟩
  · intro x
    change H (E 0 (H.symm x)) = x
    rw [hE0, H.apply_symm_apply]
  · intro x
    change H (E 1 (H.symm ((x : ℝ) : AddCircle (1 : ℝ)))) = _
    have hx : H.symm ((x : ℝ) : AddCircle (1 : ℝ)) = Quot.mk _ x := by
      apply H.injective
      rw [H.apply_symm_apply]
      exact (circleQuotHomeomorph_mk x).symm
    rw [hx, hE1, circleQuotHomeomorph_mk]

end FiniteAvalanches.Electrical.StatementGeometry
