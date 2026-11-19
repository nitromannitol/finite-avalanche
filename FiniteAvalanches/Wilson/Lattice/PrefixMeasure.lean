import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.Probability.ProductMeasure

/-! A law on a finite alphabet is determined by its consecutive prefixes. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open MeasureTheory
open scoped Classical

noncomputable section

variable {D : Type*} [Fintype D] [Nonempty D] [MeasurableSpace D] [MeasurableSingletonClass D]

/-- Finite measures on infinite words agree if all finite consecutive prefix
patterns have equal masses. -/
theorem measure_eq_of_prefix_patterns (μ ν : Measure (ℕ → D)) [IsFiniteMeasure μ]
    (h : ∀ (n : ℕ) (w : ℕ → D),
      μ {ξ | ∀ i < n, ξ i = w i} = ν {ξ | ∀ i < n, ξ i = w i}) : μ = ν := by
  have hm (F : Finset ℕ) : Measure.map F.restrict μ = Measure.map F.restrict ν := by
    let n := F.sup id + 1
    have hsub : F ⊆ Finset.range n := by
      intro i hi
      apply Finset.mem_range.mpr
      exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
    have hbig : Measure.map (Finset.range n).restrict μ =
        Measure.map (Finset.range n).restrict ν := by
      apply Measure.ext_of_singleton
      intro p
      have hmeas : Measurable ((Finset.range n).restrict : (ℕ → D) → (Finset.range n → D)) :=
        Finset.measurable_restrict _
      rw [Measure.map_apply hmeas (measurableSet_singleton p),
        Measure.map_apply hmeas (measurableSet_singleton p)]
      let w : ℕ → D := fun i => if hi : i < n then p ⟨i, Finset.mem_range.mpr hi⟩ else Classical.choice inferInstance
      have he : ((Finset.range n).restrict : (ℕ → D) → (Finset.range n → D)) ⁻¹' {p} =
          {ξ | ∀ i < n, ξ i = w i} := by
        ext ξ
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
        constructor
        · intro hp i hi
          have he := congrFun hp ⟨i, Finset.mem_range.mpr hi⟩
          simpa only [Finset.restrict_def, w, dif_pos hi] using he
        · intro hp
          funext i
          have hi := Finset.mem_range.mp i.property
          simpa only [Finset.restrict_def, w, dif_pos hi] using hp i.val hi
      rw [he]
      exact h n w
    have hc := congrArg (Measure.map (Finset.restrict₂ (π := fun _ => D) hsub)) hbig
    rw [Measure.map_map (Finset.measurable_restrict₂ hsub) (Finset.measurable_restrict _),
      Measure.map_map (Finset.measurable_restrict₂ hsub) (Finset.measurable_restrict _),
      Finset.restrict₂_comp_restrict] at hc
    exact hc
  apply Measure.ext_of_generateFrom_of_iUnion
    (measurableCylinders (fun _ : ℕ => D)) (fun _ : ℕ => (Set.univ : Set (ℕ → D)))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
    (Set.iUnion_const _) (fun _ => univ_mem_measurableCylinders _) (fun _ => measure_ne_top μ _)
  intro S hS
  obtain ⟨F, A, hA, rfl⟩ := (mem_measurableCylinders S).mp hS
  have hf : Measurable (F.restrict : (ℕ → D) → F → D) := Finset.measurable_restrict F
  simpa only [Measure.map_apply hf hA, MeasureTheory.cylinder] using
    congrArg (fun m => m A) (hm F)

end
end FiniteAvalanches.Wilson.Lattice
