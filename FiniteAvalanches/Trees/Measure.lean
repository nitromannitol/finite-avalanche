module

public import FiniteAvalanches.Trees.JoiningCounts
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

@[expose] public section

/-! Actual uniform finite measures on copied-edge tree subsets. -/
open scoped Classical ENNReal
open MeasureTheory
namespace FiniteAvalanches

noncomputable def uniformMeasure (α : Type*) [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] : Measure α :=
  (Nat.card α : ℝ≥0∞)⁻¹ • Measure.count

instance uniformMeasure_probability (α : Type*) [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    IsProbabilityMeasure (uniformMeasure α) := by
  constructor
  simp only [uniformMeasure, Measure.smul_apply, smul_eq_mul, Measure.count_univ]
  rw [ENat.card_eq_coe_natCard]
  simp [Nat.card_eq_fintype_card, ENNReal.inv_mul_cancel, Fintype.card_ne_zero]

theorem uniformMeasure_apply (α : Type*) [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (A : Set α) :
    uniformMeasure α A = (Nat.card A : ℝ≥0∞) / Nat.card α := by
  rw [uniformMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.count_apply A.toFinite.measurableSet, Set.encard, ENat.card_eq_coe_natCard]
  exact ENNReal.div_eq_inv_mul.symm

theorem uniformMeasure_real_apply (α : Type*) [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (A : Set α) :
    (uniformMeasure α).real A = (Nat.card A : ℝ) / Nat.card α := by
  simp [Measure.real, uniformMeasure_apply, ENNReal.toReal_div]

theorem integral_uniformMeasure (α : Type*) [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (f : α → ℝ) :
    (∫ x, f x ∂uniformMeasure α) = (∑ x, f x) / Nat.card α := by
  simp only [uniformMeasure, integral_smul_measure, integral_count, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul]
  ring

namespace Trees.Multigraph
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E] (G : Multigraph V E)

instance componentTreeMeasurableSpace (C : Set V) : MeasurableSpace (G.ComponentTree C) := ⊤
instance componentTreeMeasurableSingletonClass (C : Set V) :
    MeasurableSingletonClass (G.ComponentTree C) := ⟨fun _ => trivial⟩

/-- Uniform probability on actual ordinary spanning-tree edge subsets. -/
noncomputable def treeLaw [Nonempty G.SpanningTree] : Measure G.SpanningTree :=
  uniformMeasure G.SpanningTree

instance treeLaw_probability [Nonempty G.SpanningTree] : IsProbabilityMeasure G.treeLaw :=
  uniformMeasure_probability _

theorem treeLaw_real_eq_counting [Nonempty G.SpanningTree] (A : Set G.SpanningTree) :
    G.treeLaw.real A = G.uniformTreeProbability A :=
  uniformMeasure_real_apply _ A

/-- The exact joining formula is an event probability of a real finite measure. -/
theorem treeLaw_real_ancestorPastTree [Nonempty G.SpanningTree] {C S : Set V}
    (r : V) (hr : r ∉ C) (hS : S.Nonempty) (t : G.ComponentTree C) (hSC : S ⊆ C) :
    G.treeLaw.real {u | G.descendants u r (G.ancestorOf u r S hS) = C ∧
      G.internalEdges C u.val = t.val} =
      (Fintype.card (G.ComponentTree Cᶜ) : ℝ) / Fintype.card G.SpanningTree *
        (∑ v ∈ (G.componentSpan t S hSC).toFinset, (G.crossingAt C v).card) := by
  rw [G.treeLaw_real_eq_counting]
  exact G.probability_ancestorPastTree_eq_sum r hr hS t hSC

end Trees.Multigraph
end FiniteAvalanches
