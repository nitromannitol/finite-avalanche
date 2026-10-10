import FiniteAvalanches.Wilson.Lattice.LocalComparison.ColorSwapSampler
import FiniteAvalanches.Wilson.Lattice.TranslationColorLaw
import FiniteAvalanches.Wilson.Lattice.ForestEvents
import LatticeProb.Graph.Zd

set_option autoImplicit false
namespace LocalColorSwap
open LatticeProb FiniteAvalanches.Wilson.Lattice MeasureTheory
open scoped Classical BigOperators
noncomputable section

theorem option_not_eq (c : Option Bool) (b : Bool) :
    c.map Bool.not = some b ↔ c = some (!b) := by
  cases c with
  | none => simp
  | some c => cases c <;> cases b <;> simp

theorem not_eq (a b : Bool) : (!a) = b ↔ a = (!b) := by
  cases a <;> cases b <;> decide

theorem run_pattern (R : RootPair) (L : List (Site 2))
    (D : Finset (Site 2)) (p : Site 2 → Bool) (ξ : ℕ → WalkDriver) :
    (∃ st, samplerRun (initialSampler (roots R)) L ξ = some st ∧
      ∀ d ∈ D, st.colors d = some (p d)) ↔
    (∃ st, samplerRun (initialSampler R) L ξ = some st ∧
      ∀ d ∈ D, st.colors d = some (!(p d))) := by
  rw [run_initial]
  cases h : samplerRun (initialSampler R) L ξ with
  | none => simp
  | some st =>
    simp only [Option.map_some, Option.some.injEq]
    constructor
    · rintro ⟨st', rfl, hp⟩
      exact ⟨st, rfl, fun d hd => (option_not_eq _ _).mp (hp d hd)⟩
    · rintro ⟨st', rfl, hp⟩
      exact ⟨state st, rfl, fun d hd => (option_not_eq _ _).mpr (hp d hd)⟩

/-- The actual lattice laws agree on every finite color pattern after complementation. -/
theorem pattern_probability (R : RootPair) (D : Finset (Site 2)) (p : Site 2 → Bool) :
    wilsonColorLaw (roots R) {σ | ∀ d ∈ D, σ d = p d} =
      wilsonColorLaw R {σ | ∀ d ∈ D, colors σ d = p d} := by
  have he : {σ : ColorField | ∀ d ∈ D, colors σ d = p d} =
      {σ | ∀ d ∈ D, σ d = !(p d)} := by
    ext σ
    simp only [Set.mem_setOf_eq, colors, not_eq]
  rw [he, wilsonColorLaw_apply_sampler _ D.toList D p (by simp),
    wilsonColorLaw_apply_sampler _ D.toList D (fun d => !(p d)) (by simp)]
  congr 1
  ext ξ
  exact run_pattern R D.toList D p ξ

/-- Full law transport, proved from the deterministic Wilson sampler. -/
theorem law_map (R : RootPair) :
    (wilsonColorLaw R).map colors = wilsonColorLaw (roots R) := by
  apply Translation.measure_eq_of_patterns
  intro D p
  have hm : MeasurableSet {σ : ColorField | ∀ d ∈ D, σ d = p d} := by
    have he : {σ : ColorField | ∀ d ∈ D, σ d = p d} = ⋂ d ∈ D, {σ | σ d = p d} := by
      ext σ
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [he]
    exact Finset.measurableSet_biInter D (fun d _ =>
      (isClosed_eq (continuous_apply d : Continuous (fun σ : ColorField => σ d))
        continuous_const).measurableSet)
  rw [Measure.map_apply measurable_colors hm]
  exact (pattern_probability R D p).symm

theorem probability_preimage (R : RootPair) (S : Set ColorField) (hS : MeasurableSet S) :
    wilsonColorLaw (roots R) S = wilsonColorLaw R (colors ⁻¹' S) := by
  rw [← law_map, Measure.map_apply measurable_colors hS]

/-- Complementation reverses each of the four original incident contact colors. -/
theorem contacts_complement (K : Finset (Site 2)) (σ : ColorField) :
    contacts K (colors σ) + contacts K σ = 4 * K.card := by
  unfold contacts
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ x ∈ K, ∑ y ∈ nbrFinset x, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro y _
      cases h : σ y <;> simp only [colors, h, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte]
    _ = 4 * K.card := by
      simp only [Finset.sum_const, smul_eq_mul, mul_one, Graph.Zd.card_nbrFinset]
      omega

end
end LocalColorSwap
