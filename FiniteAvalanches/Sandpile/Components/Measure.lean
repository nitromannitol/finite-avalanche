import FiniteAvalanches.Sandpile.Components.SourceFields
import FiniteAvalanches.Sandpile.Components.FiniteCarriers
import FiniteAvalanches.Sandpile.Waves.Occupation
import Mathlib.MeasureTheory.Measure.Count

/-! Literal core-shape mass with the original recurrent counting normalization.
The punctured measure is finite counting measure with that common singleton
mass; it is not renormalized to probability. Tree-count equality is not assumed. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves MeasureTheory
open scoped Classical ENNReal
noncomputable section

instance puncturedMeasurableSpace {N : ℕ} {o : FiniteWired.Active N} :
    MeasurableSpace (Punctured N o) := ⊤
instance puncturedMeasurableSingletonClass {N : ℕ} {o : FiniteWired.Active N} :
    MeasurableSingletonClass (Punctured N o) := ⟨fun _ => trivial⟩

/-- Common mass is exactly the reciprocal used by the original Recurrent law. -/
def puncturedCountingMeasure {N : ℕ} (o : FiniteWired.Active N) : Measure (Punctured N o) :=
  (Fintype.card (FiniteWired.Recurrent N) : ℝ≥0∞)⁻¹ • Measure.count

theorem punctured_counting_apply {N : ℕ} (o : FiniteWired.Active N)
    (s : Set (Punctured N o)) :
    puncturedCountingMeasure o s =
      (Nat.card s : ℝ≥0∞) / Fintype.card (FiniteWired.Recurrent N) := by
  rw [puncturedCountingMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.count_apply s.toFinite.measurableSet, Set.encard, ENat.card_eq_coe_natCard]
  exact ENNReal.div_eq_inv_mul.symm

instance puncturedCountingMeasureFinite {N : ℕ} (o : FiniteWired.Active N) :
    IsFiniteMeasure (puncturedCountingMeasure o) := by
  constructor
  rw [punctured_counting_apply]
  exact ENNReal.div_lt_top (by simp) (by simp [Fintype.card_ne_zero])

theorem punctured_counting_singleton {N : ℕ} (o : FiniteWired.Active N)
    (h : Punctured N o) :
    puncturedCountingMeasure o {h} = (Fintype.card (FiniteWired.Recurrent N) : ℝ≥0∞)⁻¹ := by
  simp [puncturedCountingMeasure, Measure.smul_apply, smul_eq_mul]

theorem punctured_singleton_eq_original_law {N : ℕ} (o : FiniteWired.Active N)
    (h : Punctured N o) (η : FiniteWired.Recurrent N) :
    puncturedCountingMeasure o {h} = FiniteWired.law N {η} := by
  rw [punctured_counting_singleton, FiniteWired.law_singleton]

/-- The event is defined by the actual largest source-minus-one forbidden core. -/
def coreEvent {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) : Set (Punctured N o) :=
  {h | core h.val = C.val}

theorem card_core_graph_field {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    Nat.card (CoreField o C.val) =
      Nat.card (OuterGraphAllowed C) * Nat.card (InnerGraphAllowed C) := by
  rw [Nat.card_congr (coreGraphFieldEquiv C), Nat.card_prod]

/-- Exact finite measure mass, not a scalar ratio merely named probability. -/
theorem core_event_mass {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    puncturedCountingMeasure o (coreEvent C) =
      (Nat.card (OuterGraphAllowed C) : ℝ≥0∞) * Nat.card (InnerGraphAllowed C) /
        Fintype.card (FiniteWired.Recurrent N) := by
  rw [punctured_counting_apply]
  change (Nat.card (CoreField o C.val) : ℝ≥0∞) / _ = _
  rw [card_core_graph_field, Nat.cast_mul]

/-- Real event mass retains the original common normalization. -/
theorem core_event_mass_toReal {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    (puncturedCountingMeasure o (coreEvent C)).toReal =
      (Nat.card (OuterGraphAllowed C) : ℝ) * Nat.card (InnerGraphAllowed C) /
        Fintype.card (FiniteWired.Recurrent N) := by
  rw [core_event_mass, ENNReal.toReal_div, ENNReal.toReal_mul]
  simp only [ENNReal.toReal_natCast]

end
end FiniteAvalanches.Sandpile.Components
