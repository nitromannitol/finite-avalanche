import FiniteAvalanches.Support.Plane.RadialCircleIsotopy
import FiniteAvalanches.Support.Plane.PuncturedExtension

/-!
# Circle isotopies acting on the plane

Radial circle isotopies that fix the unit disk extend jointly across the
origin, yielding plane isotopies with jointly continuous inverse maps.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set Filter

/-- A family of punctured maps fixing a common neighborhood of zero extends
jointly continuously across zero. -/
theorem continuous_parametric_puncturedExtend {T E : Type*} [TopologicalSpace T]
    [NormedAddCommGroup E] (h : T → ({0}ᶜ : Set E) → ({0}ᶜ : Set E))
    (hc : Continuous (fun p : T × ({0}ᶜ : Set E) => h p.1 p.2))
    (hr : ∀ t (x : ({0}ᶜ : Set E)), ‖(x : E)‖ < 1 → h t x = x) :
    Continuous (fun p : T × E => puncturedExtend (h p.1) p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p.2 = 0
  · have he : (fun q : T × E => puncturedExtend (h q.1) q.2) =ᶠ[nhds p] Prod.snd := by
      have hb : {q : T × E | q.2 ∈ Metric.ball (0 : E) 1} ∈ nhds p := by
        apply (Metric.isOpen_ball.preimage continuous_snd).mem_nhds
        change p.2 ∈ Metric.ball (0 : E) 1
        simpa only [hp, Metric.mem_ball, dist_self] using (zero_lt_one : (0 : ℝ) < 1)
      filter_upwards [hb] with q hq
      by_cases hq0 : q.2 = 0
      · simp [hq0, puncturedExtend]
      · rw [puncturedExtend_of_ne _ q.2 hq0]
        have hn : ‖q.2‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hq
        exact congrArg Subtype.val (hr q.1 ⟨q.2, by simpa using hq0⟩ hn)
    exact continuous_snd.continuousAt.congr_of_eventuallyEq he
  · let U : Set (T × E) := {q | q.2 ≠ 0}
    have hU : IsOpen U := isOpen_compl_singleton.preimage continuous_snd
    have hcont : ContinuousOn (fun q : T × E => puncturedExtend (h q.1) q.2) U := by
      rw [continuousOn_iff_continuous_restrict]
      change Continuous (fun q : U => puncturedExtend (h q.val.1) q.val.2)
      have heq : (fun q : U => puncturedExtend (h q.val.1) q.val.2) =
          (fun q : U => (h q.val.1 ⟨q.val.2, by simpa only [mem_compl_iff, mem_singleton_iff] using
            (show q.val.2 ≠ 0 from q.property)⟩ : E)) := by
        funext q
        exact puncturedExtend_of_ne _ _ q.property
      rw [heq]
      let k : U → T × ({0}ᶜ : Set E) := fun q =>
        (q.val.1, ⟨q.val.2, by simpa only [mem_compl_iff, mem_singleton_iff] using
          (show q.val.2 ≠ 0 from q.property)⟩)
      have hk : Continuous k := (continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
      change Continuous (fun q : U => (h (k q).1 (k q).2 : E))
      exact continuous_subtype_val.comp (hc.comp hk)
    exact hcont.continuousAt (hU.mem_nhds hp)

/-- A punctured-plane isotopy fixing the unit disk extends to a jointly
continuous plane isotopy, including its inverse family. -/
theorem exists_plane_isotopy_of_punctured_radial_isotopy
    (H : unitInterval → ({0}ᶜ : Set ℂ) ≃ₜ ({0}ᶜ : Set ℂ))
    (hH : Continuous (fun p : unitInterval × ({0}ᶜ : Set ℂ) => H p.1 p.2))
    (hHi : Continuous (fun p : unitInterval × ({0}ᶜ : Set ℂ) => (H p.1).symm p.2))
    (hfix : ∀ s (x : ({0}ᶜ : Set ℂ)), ‖(x : ℂ)‖ ≤ 1 → H s x = x)
    (hstart : ∀ x, H 0 x = x) :
    ∃ G : unitInterval → ℂ ≃ₜ ℂ,
      Continuous (fun p : unitInterval × ℂ => G p.1 p.2) ∧
      Continuous (fun p : unitInterval × ℂ => (G p.1).symm p.2) ∧
      (∀ s x, ‖x‖ ≤ 1 → G s x = x) ∧
      (∀ x, G 0 x = x) ∧
      (∀ s (x : ({0}ᶜ : Set ℂ)), G s x = (H s x : ℂ)) := by
  have hr (s : unitInterval) (x : ({0}ᶜ : Set ℂ)) (hx : ‖(x : ℂ)‖ < 1) : H s x = x :=
    hfix s x hx.le
  have hri (s : unitInterval) (x : ({0}ᶜ : Set ℂ)) (hx : ‖(x : ℂ)‖ < 1) :
      (H s).symm x = x := by
    apply (H s).injective
    rw [(H s).apply_symm_apply]
    exact (hr s x hx).symm
  let G : unitInterval → ℂ ≃ₜ ℂ := fun s => puncturedHomeomorphExtend (H s) (hr s)
  refine ⟨G, ?_, ?_, ?_, ?_, ?_⟩
  · change Continuous (fun p : unitInterval × ℂ => puncturedExtend (H p.1) p.2)
    exact continuous_parametric_puncturedExtend (fun s => H s) hH hr
  · change Continuous (fun p : unitInterval × ℂ => puncturedExtend (H p.1).symm p.2)
    exact continuous_parametric_puncturedExtend (fun s => (H s).symm) hHi hri
  · intro s x hx
    by_cases hx0 : x = 0
    · subst x
      simp [G, puncturedHomeomorphExtend, puncturedExtend]
    · change puncturedExtend (H s) x = x
      rw [puncturedExtend_of_ne _ x hx0]
      exact congrArg Subtype.val (hfix s ⟨x, by simpa using hx0⟩ hx)
  · intro x
    by_cases hx0 : x = 0
    · subst x
      simp [G, puncturedHomeomorphExtend, puncturedExtend]
    · change puncturedExtend (H 0) x = x
      rw [puncturedExtend_of_ne _ x hx0]
      exact congrArg Subtype.val (hstart ⟨x, by simpa using hx0⟩)
  · intro s x
    change puncturedExtend (H s) (x : ℂ) = (H s x : ℂ)
    exact puncturedExtend_of_ne _ (x : ℂ) (by
      simpa only [mem_compl_iff, mem_singleton_iff] using x.property)

/-- A circle homeomorphism with increasing normalized cut is realized by a
plane isotopy that fixes the unit disk and acts by the circle map outside the
disk of radius two. -/
theorem exists_plane_isotopy_of_circle_homeomorph
    (F : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ))
    (hinc : StrictMono (circleCutMap (normalizedCircleHomeomorph F)
      (normalizedCircleHomeomorph_zero F))) :
    ∃ G : unitInterval → ℂ ≃ₜ ℂ,
      Continuous (fun p : unitInterval × ℂ => G p.1 p.2) ∧
      Continuous (fun p : unitInterval × ℂ => (G p.1).symm p.2) ∧
      (∀ s x, ‖x‖ ≤ 1 → G s x = x) ∧
      (∀ x, G 0 x = x) ∧
      (∀ s x, ‖G s x‖ = ‖x‖) ∧
      (∀ (x : ({0}ᶜ : Set ℂ)), 2 ≤ ‖(x : ℂ)‖ →
        ∃ y : ({0}ᶜ : Set ℂ), (y : ℂ) = G 1 x ∧
          (puncturedPolarCoordinates y).2 = F (puncturedPolarCoordinates x).2) := by
  obtain ⟨A, hA, hAi, hA0, hA1⟩ := exists_circle_isotopy_of_normalized_cut F hinc
  obtain ⟨H, hH, hHi, hfix, hnorm, hstart, hangle⟩ :=
    exists_punctured_radial_isotopy A hA hAi hA0
  obtain ⟨G, hG, hGi, hGfix, hGstart, hGextend⟩ :=
    exists_plane_isotopy_of_punctured_radial_isotopy H hH hHi hfix hstart
  refine ⟨G, hG, hGi, hGfix, hGstart, ?_, ?_⟩
  · intro s x
    by_cases hx : x = 0
    · subst x
      rw [hGfix s 0 (by simp)]
    · let y : ({0}ᶜ : Set ℂ) := ⟨x, by simpa using hx⟩
      change ‖G s y‖ = ‖(y : ℂ)‖
      rw [hGextend s y]
      exact hnorm s y
  · intro x hx
    refine ⟨H 1 x, (hGextend 1 x).symm, ?_⟩
    rw [hangle]
    have hc : radialCutoff (puncturedPolarCoordinates x).1 = 1 := by
      apply radialCutoff_eq_one
      simpa only [puncturedPolarCoordinates_radius] using hx
    rw [hc, mul_one, hA1]

end FiniteAvalanches.Electrical.StatementGeometry
