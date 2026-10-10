import FiniteAvalanches.Wilson.Lattice.TranslationSampler
import Mathlib.MeasureTheory.Constructions.Cylinders

/-! Exact pushforward covariance of the uniquely characterized Wilson color law,
proved from every finite color pattern of its actual deterministic iid-row sampler. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.Translation
open LatticeProb MeasureTheory
open scoped Classical
noncomputable section

theorem run_pattern (R : RootPair) (z : Site 2) (L : List (Site 2))
    (D : Finset (Site 2)) (p : Site 2 → Bool) (ξ : ℕ → WalkDriver) :
    (∃ st, samplerRun (initialSampler (roots R z)) (L.map (fun x => x + z)) ξ = some st ∧
      ∀ d ∈ D, st.colors (d + z) = some (p d)) ↔
    (∃ st, samplerRun (initialSampler R) L ξ = some st ∧
      ∀ d ∈ D, st.colors d = some (p d)) := by
  constructor
  · rintro ⟨st, hs, hd⟩
    have hc (v : Site 2) : (initialSampler R).colors (v + -z) =
        (initialSampler (roots R z)).colors v := by
      simpa only [neg_add_cancel_right] using (initial_colors R z (v + -z)).symm
    obtain ⟨out, ho, hc'⟩ := run_success (-z) hc _ ξ hs
    have hl : (L.map (fun x => x + z)).map (fun x => x + -z) = L := by
      simp only [List.map_map, Function.comp_def, add_neg_cancel_right, List.map_id']
    rw [hl] at ho
    refine ⟨out, ho, ?_⟩
    intro d hD
    have he := hc' (d + z)
    rw [add_neg_cancel_right] at he
    exact he.trans (hd d hD)
  · rintro ⟨st, hs, hd⟩
    obtain ⟨out, ho, hc⟩ := run_success z (initial_colors R z) L ξ hs
    exact ⟨out, ho, fun d hD => (hc d).trans (hd d hD)⟩

/-- Every finite full-field pattern, with no enumeration restriction. -/
theorem pattern_probability (R : RootPair) (z : Site 2) (D : Finset (Site 2))
    (p : Site 2 → Bool) :
    wilsonColorLaw (roots R z) {σ | ∀ d ∈ D, σ d = p d} =
      wilsonColorLaw R {σ | ∀ d ∈ D, colors z σ d = p d} := by
  let F := D.image (fun d => d - z)
  let q := fun x : Site 2 => p (x + z)
  have hD : F.image (fun x => x + z) = D := by
    simp only [F, Finset.image_image, Function.comp_def, sub_add_cancel, Finset.image_id']
  have hpattern : {σ : ColorField | ∀ d ∈ D, colors z σ d = p d} =
      {σ | ∀ x ∈ F, σ x = q x} := by
    ext σ
    constructor
    · intro h x hx
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      simpa only [colors, q, sub_add_cancel] using h d hd
    · intro h d hd
      have he := h (d - z) (Finset.mem_image.mpr ⟨d, hd, rfl⟩)
      simpa only [colors, q, sub_add_cancel] using he
  have hm : ∀ d ∈ D, d ∈ F.toList.map (fun x => x + z) := by
    intro d hd
    rw [← hD] at hd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    exact List.mem_map.mpr ⟨x, Finset.mem_toList.mpr hx, rfl⟩
  rw [wilsonColorLaw_apply_sampler _ _ _ _ hm, hpattern,
    wilsonColorLaw_apply_sampler _ _ _ _ (fun d hd => Finset.mem_toList.mpr hd)]
  congr 1
  ext ξ
  have he : (∃ st, samplerRun (initialSampler (roots R z))
      (F.toList.map (fun x => x + z)) ξ = some st ∧
      ∀ d ∈ D, st.colors d = some (p d)) ↔
      (∃ st, samplerRun (initialSampler (roots R z))
      (F.toList.map (fun x => x + z)) ξ = some st ∧
      ∀ x ∈ F, st.colors (x + z) = some (q x)) := by
    constructor
    · rintro ⟨st, hs, hd⟩
      exact ⟨st, hs, fun x hx => hd (x + z) (hD ▸ Finset.mem_image.mpr ⟨x, hx, rfl⟩)⟩
    · rintro ⟨st, hs, hd⟩
      refine ⟨st, hs, ?_⟩
      intro d hmem
      rw [← hD] at hmem
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hmem
      exact hd x hx
  exact he.trans (run_pattern R z F.toList F q ξ)

/-- Finite Boolean patterns determine the entire measure on the full product carrier. -/
theorem measure_eq_of_patterns (μ ν : Measure ColorField) [IsFiniteMeasure μ]
    (h : ∀ (F : Finset (Site 2)) (p : Site 2 → Bool),
      μ {σ | ∀ x ∈ F, σ x = p x} = ν {σ | ∀ x ∈ F, σ x = p x}) : μ = ν := by
  have hm (F : Finset (Site 2)) : Measure.map F.restrict μ = Measure.map F.restrict ν := by
    apply Measure.ext_of_singleton
    intro p
    have hf : Measurable (F.restrict : ColorField → F → Bool) :=
      measurable_pi_lambda _ (fun x => measurable_pi_apply x.val)
    obtain ⟨q, hq⟩ := (Subtype.val_injective : Function.Injective
      (Subtype.val : F → Site 2)).surjective_comp_right p
    have he : {σ : ColorField | F.restrict σ = p} = {σ | ∀ x ∈ F, σ x = q x} := by
      ext σ
      constructor
      · intro hs x hx
        exact (congrFun hs ⟨x, hx⟩).trans (congrFun hq ⟨x, hx⟩).symm
      · intro hs
        funext x
        exact (hs x.val x.property).trans (congrFun hq x)
    rw [Measure.map_apply hf (measurableSet_singleton p),
      Measure.map_apply hf (measurableSet_singleton p)]
    change μ {σ | F.restrict σ = p} = ν {σ | F.restrict σ = p}
    rw [he]
    exact h F q
  apply Measure.ext_of_generateFrom_of_iUnion
    (measurableCylinders (fun _ : Site 2 => Bool)) (fun _ : ℕ => (Set.univ : Set ColorField))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
    (Set.iUnion_const _) (fun _ => univ_mem_measurableCylinders _) (fun _ => measure_ne_top μ _)
  intro S hS
  obtain ⟨F, A, hA, rfl⟩ := (mem_measurableCylinders S).mp hS
  have hf : Measurable (F.restrict : ColorField → F → Bool) :=
    measurable_pi_lambda _ (fun x => measurable_pi_apply x.val)
  simpa only [Measure.map_apply hf hA, cylinder] using congrArg (fun m => m A) (hm F)

/-- Exact law equality for every RootPair and shift, using the campaign's unique
Wilson law and all original sites. Covariance is a conclusion, never a premise. -/
theorem wilsonColorLaw_map (R : RootPair) (z : Site 2) :
    (wilsonColorLaw R).map (colors z) = wilsonColorLaw (roots R z) := by
  apply measure_eq_of_patterns
  intro F p
  have hm : MeasurableSet {σ : ColorField | ∀ x ∈ F, σ x = p x} := by
    have he : {σ : ColorField | ∀ x ∈ F, σ x = p x} = ⋂ x ∈ F, {σ | σ x = p x} := by
      ext σ; simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [he]
    exact Finset.measurableSet_biInter F (fun x _ =>
      (isClosed_eq (continuous_apply x : Continuous (fun σ : ColorField => σ x))
        continuous_const).measurableSet)
  rw [Measure.map_apply (measurable_colors z) hm]
  exact (pattern_probability R z F p).symm

end
end FiniteAvalanches.Wilson.Lattice.Translation
