import FiniteAvalanches.Sandpile.Measurability
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Extended observables retain infinity on nonstabilizing configurations. -/
namespace FiniteAvalanches
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile MeasureTheory
open scoped ENNReal Classical
noncomputable section

/-- Lattice translation of the entire stable height field. -/
def translate (z : Site2) (η : StableField) : StableField := fun x => η (x + z)

theorem measurable_translate (z : Site2) : Measurable (translate z) := by
  apply measurable_pi_lambda
  intro x
  exact measurable_pi_apply (x + z)

/-- The exact extended nonnegative value of a natural count, retaining infinity. -/
def extendedCount (n : WithTop ℕ) : ℝ≥0∞ :=
  match n with
  | none => ⊤
  | some k => k

theorem extendedCount_top : extendedCount ⊤ = ⊤ := rfl

theorem extendedCount_coe (n : ℕ) : extendedCount (n : WithTop ℕ) = n := rfl

theorem ofReal_lt_extendedCount_coe (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    ENNReal.ofReal R < extendedCount (n : WithTop ℕ) ↔ R < (n : ℝ) := by
  simpa [extendedCount] using
    (ENNReal.ofReal_lt_iff_lt_toReal hR (ENNReal.natCast_ne_top n))

theorem ofReal_lt_extendedCount_top (R : ℝ) :
    ENNReal.ofReal R < extendedCount ⊤ := ENNReal.ofReal_lt_top

/-- The positive-power logarithmic moment integrand, with value infinity at infinity. -/
def logMomentIntegrand (p : {p : ℝ // 0 < p}) (n : WithTop ℕ) : ℝ≥0∞ :=
  match n with
  | none => ⊤
  | some k => ENNReal.ofReal (Real.log (2 + (k : ℝ)) ^ p.val)

theorem logMomentIntegrand_top (p : {p : ℝ // 0 < p}) :
    logMomentIntegrand p ⊤ = ⊤ := rfl

theorem logMomentIntegrand_coe (p : {p : ℝ // 0 < p}) (n : ℕ) :
    logMomentIntegrand p (n : WithTop ℕ) =
      ENNReal.ofReal (Real.log (2 + (n : ℝ)) ^ p.val) := rfl

theorem measurable_extendedCount : Measurable extendedCount := measurable_of_countable _

theorem measurable_logMomentIntegrand (p : {p : ℝ // 0 < p}) :
    Measurable (logMomentIntegrand p) := measurable_of_countable _

theorem measurable_radius_extended (o : Site2) :
    Measurable (fun η : StableField => extendedCount (radius η o)) :=
  measurable_extendedCount.comp (measurable_radius o)

theorem measurable_totalTopplings_extended (o : Site2) :
    Measurable (fun η : StableField => extendedCount (totalTopplings η o)) :=
  measurable_extendedCount.comp (measurable_totalTopplings o)

theorem measurableSet_radius_tail (o : Site2) (R : ℝ) :
    MeasurableSet {η : StableField | ENNReal.ofReal R < extendedCount (radius η o)} :=
  measurableSet_lt measurable_const (measurable_radius_extended o)

theorem measurableSet_totalTopplings_tail (o : Site2) (R : ℝ) :
    MeasurableSet {η : StableField |
      ENNReal.ofReal R < extendedCount (totalTopplings η o)} :=
  measurableSet_lt measurable_const (measurable_totalTopplings_extended o)

theorem measurable_radius_logMoment (o : Site2) (p : {p : ℝ // 0 < p}) :
    Measurable (fun η : StableField => logMomentIntegrand p (radius η o)) :=
  (measurable_logMomentIntegrand p).comp (measurable_radius o)

theorem measurable_totalTopplings_logMoment (o : Site2) (p : {p : ℝ // 0 < p}) :
    Measurable (fun η : StableField => logMomentIntegrand p (totalTopplings η o)) :=
  (measurable_logMomentIntegrand p).comp
    (measurable_totalTopplings o)

end
end FiniteAvalanches
