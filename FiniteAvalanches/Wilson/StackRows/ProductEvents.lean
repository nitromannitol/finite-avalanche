import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure

/-! Two elementary facts about product probability spaces used for Wilson's algorithm.
Events of an infinite product of probability spaces which depend on disjoint sets of
coordinates are independent. A probability splits along a countable disjoint family of
first-step events, with the complementary event contributing one minus their masses. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CopiedNetwork

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- An event depending only on the coordinates in `S` is measurable for the coordinate
σ-algebra of `S`. -/
theorem measurableSet_iSup_of_depends (S : Set ι) (ω₀ : (i : ι) → X i)
    (A : Set ((i : ι) → X i)) (hAm : MeasurableSet A)
    (hA : ∀ ω ω' : (i : ι) → X i, (∀ i ∈ S, ω i = ω' i) → (ω ∈ A ↔ ω' ∈ A)) :
    MeasurableSet[⨆ i ∈ S, MeasurableSpace.comap (fun ω : (i : ι) → X i => ω i) inferInstance] A := by
  classical
  let e : ((i : ι) → X i) → (i : ι) → X i := fun ω i => if i ∈ S then ω i else ω₀ i
  have hle : MeasurableSpace.comap e MeasurableSpace.pi ≤
      ⨆ i ∈ S, MeasurableSpace.comap (fun ω : (i : ι) → X i => ω i) inferInstance := by
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    apply iSup_le
    intro i
    rw [MeasurableSpace.comap_comp]
    by_cases hi : i ∈ S
    · have hf : (fun ω : (i : ι) → X i => ω i) ∘ e = fun ω => ω i := by
        funext ω
        simp [e, hi]
      rw [hf]
      exact le_iSup₂_of_le i hi le_rfl
    · have hf : (fun ω : (i : ι) → X i => ω i) ∘ e = fun _ => ω₀ i := by
        funext ω
        simp [e, hi]
      rw [hf, MeasurableSpace.comap_const]
      exact bot_le
  have hpre : e ⁻¹' A = A := by
    ext ω
    simp only [Set.mem_preimage]
    apply hA
    intro i hi
    simp only [e, hi, if_true]
  rw [← hpre]
  exact hle _ ⟨A, hAm, rfl⟩

variable (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- Measurable events of a product probability space which depend on disjoint sets of
coordinates are independent. -/
theorem infinitePi_inter_eq_mul_of_disjoint (S T : Set ι) (hST : Disjoint S T)
    (ω₀ : (i : ι) → X i) (A B : Set ((i : ι) → X i))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hA : ∀ ω ω' : (i : ι) → X i, (∀ i ∈ S, ω i = ω' i) → (ω ∈ A ↔ ω' ∈ A))
    (hB : ∀ ω ω' : (i : ι) → X i, (∀ i ∈ T, ω i = ω' i) → (ω ∈ B ↔ ω' ∈ B)) :
    Measure.infinitePi μ (A ∩ B) = Measure.infinitePi μ A * Measure.infinitePi μ B := by
  let m : ι → MeasurableSpace ((i : ι) → X i) := fun i =>
    MeasurableSpace.comap (fun ω : (i : ι) → X i => ω i) inferInstance
  have hm : ∀ i, m i ≤ (inferInstance : MeasurableSpace ((i : ι) → X i)) :=
    fun i => (measurable_pi_apply i).comap_le
  have hi : iIndep m (Measure.infinitePi μ) :=
    (iIndepFun_infinitePi (X := fun _ a => a) (P := μ) (fun _ => measurable_id)).iIndep
  have h := indep_iSup_of_disjoint hm hi hST
  exact (Indep_iff _ _ _).mp h A B (measurableSet_iSup_of_depends S ω₀ A hAm hA)
    (measurableSet_iSup_of_depends T ω₀ B hBm hB)

omit [∀ i, MeasurableSpace (X i)] in
/-- A probability split along a countable disjoint family of first-step events. -/
theorem measure_firstStep {Ω κ : Type*} [MeasurableSpace Ω] [Countable κ] (P : Measure Ω)
    [IsProbabilityMeasure P] (A C : κ → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (hC : ∀ i, MeasurableSet (C i)) (hd : Pairwise (Function.onFun Disjoint A)) (b : Prop)
    [Decidable b] (S : Set Ω) (hS : S = (⋃ i, A i ∩ C i) ∪ ((⋃ i, A i)ᶜ ∩ {_ω | b})) :
    MeasurableSet S ∧
      P S = (∑' i, P (A i ∩ C i)) + if b then 1 - ∑' i, P (A i) else 0 := by
  have hU : MeasurableSet (⋃ i, A i) := MeasurableSet.iUnion hA
  have hb : MeasurableSet {_ω : Ω | b} := by
    by_cases h : b
    · simp only [h, Set.setOf_true, MeasurableSet.univ]
    · simp only [h, Set.setOf_false, MeasurableSet.empty]
  have hAC : MeasurableSet (⋃ i, A i ∩ C i) := MeasurableSet.iUnion (fun i => (hA i).inter (hC i))
  refine ⟨hS ▸ hAC.union (hU.compl.inter hb), ?_⟩
  have hdis : Disjoint (⋃ i, A i ∩ C i) ((⋃ i, A i)ᶜ ∩ {_ω | b}) := by
    rw [Set.disjoint_left]
    intro ω hω hω'
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hω
    exact hω'.1 (Set.mem_iUnion.mpr ⟨i, hi.1⟩)
  have hdAC : Pairwise (Function.onFun Disjoint (fun i => A i ∩ C i)) := by
    intro i j hij
    exact (hd hij).mono Set.inter_subset_left Set.inter_subset_left
  rw [hS, measure_union hdis (hU.compl.inter hb), measure_iUnion hdAC (fun i => (hA i).inter (hC i))]
  congr 1
  by_cases h : b
  · simp only [h, Set.setOf_true, Set.inter_univ, if_true]
    rw [prob_compl_eq_one_sub hU, measure_iUnion hd hA]
  · simp only [h, Set.setOf_false, Set.inter_empty, measure_empty, if_false]

end FiniteAvalanches.Wilson.CopiedNetwork
