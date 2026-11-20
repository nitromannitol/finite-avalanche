import FiniteAvalanches.Support.Plane.AnnulusRotation

/-!
# Extending a punctured homeomorphism

A homeomorphism of a punctured normed space that fixes a neighborhood of the
puncture extends to a homeomorphism of the whole space.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

variable {E : Type*} [NormedAddCommGroup E]

/-- Extend a punctured map by fixing the origin. -/
noncomputable def puncturedExtend (h : ({0}ᶜ : Set E) → ({0}ᶜ : Set E)) (x : E) : E := by
  by_cases hx : x = 0
  · exact 0
  · exact (h ⟨x, by simpa using hx⟩ : E)

/-- The extension agrees with the punctured map away from zero. -/
theorem puncturedExtend_of_ne (h : ({0}ᶜ : Set E) → ({0}ᶜ : Set E))
    (x : E) (hx : x ≠ 0) :
    puncturedExtend h x = h ⟨x, by simpa using hx⟩ := by
  simp only [puncturedExtend, dif_neg hx]

/-- A continuous punctured map that fixes a neighborhood of zero extends
continuously to the origin. -/
theorem continuous_puncturedExtend (h : ({0}ᶜ : Set E) → ({0}ᶜ : Set E))
    (hc : Continuous h) (hr : ∀ x : ({0}ᶜ : Set E), ‖(x : E)‖ < 1 → h x = x) :
    Continuous (puncturedExtend h) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have he : puncturedExtend h =ᶠ[nhds (0 : E)] id := by
      filter_upwards [Metric.ball_mem_nhds (0 : E) zero_lt_one] with y hy
      by_cases hy0 : y = 0
      · subst y
        simp [puncturedExtend]
      · rw [puncturedExtend_of_ne h y hy0]
        have hynorm : ‖y‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hy
        exact congrArg Subtype.val (hr ⟨y, by simpa using hy0⟩ hynorm)
    exact continuousAt_id.congr_of_eventuallyEq he
  · have hcont : ContinuousOn (puncturedExtend h) ({0}ᶜ : Set E) := by
      rw [continuousOn_iff_continuous_restrict]
      have heq : (fun x : ({0}ᶜ : Set E) => puncturedExtend h x) =
          (fun x : ({0}ᶜ : Set E) => (h x : E)) := by
        funext x
        exact puncturedExtend_of_ne h x (by simpa only [mem_compl_iff, mem_singleton_iff] using x.property)
      change Continuous (fun x : ({0}ᶜ : Set E) => puncturedExtend h x)
      rw [heq]
      exact continuous_subtype_val.comp hc
    exact hcont.continuousAt (isOpen_compl_singleton.mem_nhds (by simpa using hx))

/-- A punctured homeomorphism that fixes the unit ball extends
to a homeomorphism of the ambient normed group. -/
noncomputable def puncturedHomeomorphExtend
    (h : ({0}ᶜ : Set E) ≃ₜ ({0}ᶜ : Set E))
    (hr : ∀ x : ({0}ᶜ : Set E), ‖(x : E)‖ < 1 → h x = x) : E ≃ₜ E := by
  have hri : ∀ x : ({0}ᶜ : Set E), ‖(x : E)‖ < 1 → h.symm x = x := by
    intro x hx
    apply h.injective
    rw [h.apply_symm_apply]
    exact (hr x hx).symm
  refine ⟨⟨puncturedExtend h, puncturedExtend h.symm, ?_, ?_⟩,
    continuous_puncturedExtend h h.continuous hr,
    continuous_puncturedExtend h.symm h.symm.continuous hri⟩
  · intro x
    by_cases hx : x = 0
    · subst x
      simp [puncturedExtend]
    · have hne : (h ⟨x, by simpa using hx⟩ : E) ≠ 0 := by
        simpa only [mem_compl_iff, mem_singleton_iff] using
          (h ⟨x, by simpa using hx⟩).property
      rw [puncturedExtend_of_ne h x hx, puncturedExtend_of_ne h.symm _ hne]
      exact congrArg Subtype.val (h.symm_apply_apply ⟨x, by simpa using hx⟩)
  · intro x
    by_cases hx : x = 0
    · subst x
      simp [puncturedExtend]
    · have hne : (h.symm ⟨x, by simpa using hx⟩ : E) ≠ 0 := by
        simpa only [mem_compl_iff, mem_singleton_iff] using
          (h.symm ⟨x, by simpa using hx⟩).property
      rw [puncturedExtend_of_ne h.symm x hx, puncturedExtend_of_ne h _ hne]
      exact congrArg Subtype.val (h.apply_symm_apply ⟨x, by simpa using hx⟩)

end FiniteAvalanches.Electrical.StatementGeometry
