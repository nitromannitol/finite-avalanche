import FiniteAvalanches.Sandpile.Limit.HeightConvergence
import FiniteAvalanches.Probability.FieldCylinders
import FiniteAvalanches.Probability.Radius.Cylinders
import FiniteAvalanches.Sandpile.ExtendedObservables
import Mathlib.MeasureTheory.Measure.Prokhorov

/-! The infinite-volume sandpile law on `ℤ²` (Athreya–Járai): the uniform recurrent laws of
finite volumes converge weakly along every exhaustion of `ℤ²` to one law, which is
translation invariant.

The cylinder probabilities converge along every exhaustion to limits that do not depend on
the exhaustion; compactness of the space of laws on height fields and determination by
cylinders then give weak convergence. Translating a volume translates its law, and translated
boxes again exhaust `ℤ²`. -/

set_option autoImplicit false

namespace FiniteAvalanches.Sandpile.InfiniteVolume

open LatticeProb MeasureTheory Filter Topology FiniteAvalanches.Trees FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Sandpile.GammaGraph FiniteAvalanches.Probability
open FiniteAvalanches.External.SandpileLimit
open scoped Classical ENNReal

noncomputable section

/-- The limit of the probability that the heights on `F` agree with `ζ`. -/
def cylinderLimit (F : Finset Site2) (ζ : StableField) : ℝ≥0∞ :=
  if F.Nonempty then ENNReal.ofReal (heightLimit F fun x => (ζ x).val) else 1

theorem cylinder_eq_heightEvent (F : Finset Site2) (ζ : StableField) :
    {η : StableField | ∀ x ∈ F, η x = ζ x} = heightEvent F fun x => (ζ x).val := by
  ext η
  simp only [Set.mem_setOf_eq, heightEvent, Fin.val_inj]

theorem isClopen_cylinder' (F : Finset Site2) (ζ : StableField) :
    IsClopen {η : StableField | ∀ x ∈ F, η x = ζ x} :=
  isClopen_finite_coordinate_event F _ fun η η' h => by
    simp only [Set.mem_setOf_eq]
    exact forall₂_congr fun x hx => by rw [h x hx]

/-- Cylinder probabilities converge along every exhaustion. -/
theorem tendsto_cylinder {Λ : ℕ → Finset Site2} (hΛ : IsExhaustion Λ) (F : Finset Site2)
    (ζ : StableField) :
    Tendsto (fun n => finiteFieldLawOn (Λ n) {η | ∀ x ∈ F, η x = ζ x}) atTop
      (𝓝 (cylinderLimit F ζ)) := by
  by_cases hF : F.Nonempty
  · rw [cylinderLimit, if_pos hF, cylinder_eq_heightEvent]
    have h := (ENNReal.tendsto_ofReal (tendsto_heightEvent_toReal hΛ hF fun x => (ζ x).val))
    refine h.congr fun n => ?_
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  · rw [cylinderLimit, if_neg hF]
    have he : {η : StableField | ∀ x ∈ F, η x = ζ x} = Set.univ := by
      rw [Finset.not_nonempty_iff_eq_empty] at hF
      subst hF
      ext η
      simp
    simp only [he, measure_univ]
    exact tendsto_const_nhds

/-- Every weak cluster point along an exhaustion has the limiting cylinder probabilities. -/
theorem clusterPt_cylinder {Λ : ℕ → Finset Site2} (hΛ : IsExhaustion Λ)
    (μ : ProbabilityMeasure StableField)
    (hμ : MapClusterPt μ atTop fun n => finiteFieldProbabilityOn (Λ n)) (F : Finset Site2)
    (ζ : StableField) : (μ : Measure StableField) {η | ∀ x ∈ F, η x = ζ x} = cylinderLimit F ζ := by
  obtain ⟨U, hU, hweak⟩ := mapClusterPt_iff_ultrafilter.mp hμ
  have h1 := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hweak
    (E := {η | ∀ x ∈ F, η x = ζ x})
    (by rw [(isClopen_cylinder' F ζ).frontier_eq]; exact measure_empty)
  exact tendsto_nhds_unique h1 ((tendsto_cylinder hΛ F ζ).mono_left hU)

theorem exists_cylinderLimit_law :
    ∃ μ : ProbabilityMeasure StableField, ∀ (F : Finset Site2) (ζ : StableField),
      (μ : Measure StableField) {η | ∀ x ∈ F, η x = ζ x} = cylinderLimit F ζ := by
  obtain ⟨μ, -, hμ⟩ := (isCompact_univ : IsCompact (Set.univ :
    Set (ProbabilityMeasure StableField))).exists_mapClusterPt
      (f := atTop) (u := fun n => finiteFieldProbabilityOn (boxSites n)) (by simp)
  exact ⟨μ, clusterPt_cylinder isExhaustion_boxSites μ hμ⟩

/-- A law with the limiting cylinder probabilities is the weak limit along every exhaustion. -/
theorem isInfiniteVolumeLaw_of_cylinders (μ : ProbabilityMeasure StableField)
    (hμ : ∀ (F : Finset Site2) (ζ : StableField),
      (μ : Measure StableField) {η | ∀ x ∈ F, η x = ζ x} = cylinderLimit F ζ) :
    IsInfiniteVolumeLaw μ := by
  intro Λ hΛ
  apply tendsto_nhds_of_unique_mapClusterPt
  intro μ' hμ'
  apply ProbabilityMeasure.toMeasure_injective
  apply measure_eq_of_field_cylinders
  intro F ζ
  rw [clusterPt_cylinder hΛ μ' hμ' F ζ, hμ F ζ]

/-! Translation. -/

theorem degree_image_add (A : Finset Site2) (x z : Site2) :
    Waves.degree (A.image (· + z)) (x + z) = Waves.degree A x := by
  unfold Waves.degree
  have he : nbrFinset (x + z) ∩ A.image (· + z) = (nbrFinset x ∩ A).image (· + z) := by
    ext y
    simp only [Finset.mem_inter, Finset.mem_image, FiniteWired.mem_neighbors_iff]
    constructor
    · rintro ⟨hxy, w, hw, rfl⟩
      refine ⟨w, ⟨?_, hw⟩, rfl⟩
      obtain ⟨i, h | h⟩ := hxy
      · exact ⟨i, Or.inl (add_right_cancel (h.trans (add_right_comm _ _ _)))⟩
      · exact ⟨i, Or.inr (add_right_cancel (h.trans (add_right_comm _ _ _)))⟩
    · rintro ⟨w, ⟨hxw, hw⟩, rfl⟩
      refine ⟨?_, w, hw, rfl⟩
      obtain ⟨i, h | h⟩ := hxw
      · exact ⟨i, Or.inl (by rw [h]; abel)⟩
      · exact ⟨i, Or.inr (by rw [h]; abel)⟩
  rw [he, Finset.card_image_of_injective _ (add_left_injective z)]

theorem translate_mem_allowedFields {Γ : Finset Site2} (z : Site2) {η : StableField}
    (hη : η ∈ allowedFields Γ) : FiniteAvalanches.translate z η ∈ allowedFields (Γ.image (· - z)) := by
  refine ⟨fun x hx => hη.1 _ fun hxz => hx (Finset.mem_image.mpr ⟨x + z, hxz, by abel⟩), ?_⟩
  intro A hA hf
  apply hη.2 (A.image (· + z))
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨w, hw, hwx⟩ := Finset.mem_image.mp (hA hx)
    rw [← hwx]
    simpa using hw
  · refine ⟨hf.1.image _, fun y hy => ?_⟩
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [degree_image_add]
    exact hf.2 x hx

theorem image_sub_image_add (Γ : Finset Site2) (z : Site2) :
    (Γ.image (· - z)).image (· - -z) = Γ := by
  rw [Finset.image_image]
  convert Finset.image_id (s := Γ)
  funext x
  simp

/-- Translation of allowed fields. -/
def translateEquiv (Γ : Finset Site2) (z : Site2) :
    allowedFields Γ ≃ allowedFields (Γ.image (· - z)) :=
  Equiv.ofBijective (fun η => ⟨FiniteAvalanches.translate z η.val, translate_mem_allowedFields z η.property⟩)
    ⟨fun η η' h => by
      apply Subtype.ext
      funext x
      have := congrFun (congrArg Subtype.val h) (x - z)
      simpa [FiniteAvalanches.translate] using this,
     fun η => by
      have hmem := translate_mem_allowedFields (-z) η.property
      rw [image_sub_image_add] at hmem
      refine ⟨⟨FiniteAvalanches.translate (-z) η.val, hmem⟩, Subtype.ext ?_⟩
      funext x
      simp [FiniteAvalanches.translate]⟩

theorem finiteFieldLawOn_image_sub (Γ : Finset Site2) (z : Site2) :
    finiteFieldLawOn (Γ.image (· - z)) = (finiteFieldLawOn Γ).map (FiniteAvalanches.translate z) := by
  rw [finiteFieldLawOn, finiteFieldLawOn, Measure.map_map (measurable_translate z)
    (measurable_of_countable _)]
  have hc : FiniteAvalanches.translate z ∘ (Subtype.val : allowedFields Γ → StableField) =
      Subtype.val ∘ translateEquiv Γ z := rfl
  rw [hc, ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    FiniteAvalanches.uniform_measure_map_equiv]

theorem continuous_translate (z : Site2) : Continuous (FiniteAvalanches.translate z) :=
  continuous_pi fun x => continuous_apply (x + z)

theorem isExhaustion_image_sub {Λ : ℕ → Finset Site2} (hΛ : IsExhaustion Λ) (z : Site2) :
    IsExhaustion fun n => (Λ n).image (· - z) := by
  intro F
  filter_upwards [hΛ (F.image (· + z))] with n hn
  intro x hx
  exact Finset.mem_image.mpr ⟨x + z, hn (Finset.mem_image_of_mem _ hx), by abel⟩

theorem map_translate_eq {μ : ProbabilityMeasure StableField} (hμ : IsInfiniteVolumeLaw μ)
    (z : Site2) : (μ : Measure StableField).map (FiniteAvalanches.translate z) = μ := by
  have h1 := hμ _ (isExhaustion_image_sub isExhaustion_boxSites z)
  have h2 := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (hμ _ isExhaustion_boxSites) (continuous_translate z)
  have he : (fun n => finiteFieldProbabilityOn ((boxSites n).image (· - z))) =
      fun n => (finiteFieldProbabilityOn (boxSites n)).map
        (continuous_translate z).measurable.aemeasurable := by
    funext n
    apply ProbabilityMeasure.toMeasure_injective
    exact finiteFieldLawOn_image_sub (boxSites n) z
  rw [he] at h1
  have := tendsto_nhds_unique h2 h1
  exact congrArg ProbabilityMeasure.toMeasure this

/-- An infinite-volume law is translation invariant. -/
theorem isTranslationInvariant_of_isInfiniteVolumeLaw {μ : ProbabilityMeasure StableField}
    (hμ : IsInfiniteVolumeLaw μ) : IsTranslationInvariant μ := by
  intro z
  have hf : _root_.translate z = FiniteAvalanches.translate (-z) := by
    funext η x
    simp [FiniteAvalanches.translate, sub_eq_add_neg]
  rw [hf]
  exact map_translate_eq hμ (-z)

/-- Athreya–Járai (2004), Theorem 1 and Remark 1(iii) with the 2006 correction (d = 2);
Járai–Werning (2014), Theorem 3: the infinite-volume sandpile law exists and is
translation invariant. -/
theorem exists_infiniteVolumeLaw_proof :
    ∃ μ : ProbabilityMeasure StableField, IsInfiniteVolumeLaw μ ∧ IsTranslationInvariant μ := by
  obtain ⟨μ, hμ⟩ := exists_cylinderLimit_law
  have hlaw := isInfiniteVolumeLaw_of_cylinders μ hμ
  exact ⟨μ, hlaw, isTranslationInvariant_of_isInfiniteVolumeLaw hlaw⟩

end

end FiniteAvalanches.Sandpile.InfiniteVolume
