import FiniteAvalanches.Sandpile.Components.Partition
import FiniteAvalanches.Sandpile.Components.Conditioning

/-! The actual core partition gives a finite conditional sum identity. Original
recurrent normalization is retained; only populated whole fibers carry probability.
No transition, graph-burning law or tree-count conclusion is an input. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Sandpile.Waves MeasureTheory
open scoped Classical ENNReal
noncomputable section
variable {N : ℕ} {o : FiniteWired.Active N}

/-- Exactly the actual source-containing shapes whose complete core fibers are populated. -/
abbrev PopulatedCoreShape (o : FiniteWired.Active N) :=
  {C : ComponentShape o // Nonempty (CoreField o C.val)}

/-- Genuine uniform probability on the entire actual core fiber. -/
def coreFiberLaw (C : PopulatedCoreShape o) : Measure (CoreField o C.val.val) := by
  letI := C.property
  exact FiniteAvalanches.uniformMeasure (CoreField o C.val.val)

instance coreFiberLaw_probability (C : PopulatedCoreShape o) : IsProbabilityMeasure (coreFiberLaw C) := by
  letI := C.property
  exact FiniteAvalanches.uniformMeasure_probability _

/-- Positive original core-event mass is precisely populated-fiber formation. -/
theorem core_event_pos_iff_nonempty (C : ComponentShape o) :
    0 < puncturedCountingMeasure o (coreEvent C) ↔ Nonempty (CoreField o C.val) := by
  rw [punctured_counting_apply]
  change 0 < (Nat.card (CoreField o C.val) : ℝ≥0∞) / Fintype.card (FiniteWired.Recurrent N) ↔ _
  rw [ENNReal.div_pos_iff, and_iff_left (ENNReal.natCast_ne_top _)]
  simp only [Nat.cast_ne_zero]
  apply Nat.pos_iff_ne_zero.symm.trans
  exact ⟨fun h => (Nat.card_pos_iff.mp h).1, fun h => Nat.card_pos_iff.mpr ⟨h, inferInstance⟩⟩

/-- Inclusion into the original punctured carrier gives its true shape-only conditional measure. -/
theorem core_fiber_law_conditioning (C : PopulatedCoreShape o) :
    (coreFiberLaw C).map Subtype.val =
      ProbabilityTheory.cond (puncturedCountingMeasure o) (coreEvent C.val) := by
  letI := C.property
  exact core_shape_conditioning C.val

/-- Every shape has its original counting mass, including zero-mass empty fibers. -/
theorem core_event_real_eq_card (C : ComponentShape o) :
    (puncturedCountingMeasure o).real (coreEvent C) =
      (Nat.card (CoreField o C.val) : ℝ) / Fintype.card (FiniteWired.Recurrent N) := by
  change (puncturedCountingMeasure o (coreEvent C)).toReal = _
  rw [punctured_counting_apply, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast]
  rfl

/-- Whole-fiber event probabilities cancel only the fiber cardinal, retaining the original denominator. -/
theorem core_mass_mul_fiber_probability (C : PopulatedCoreShape o)
    (s : Set (CoreField o C.val.val)) :
    (puncturedCountingMeasure o).real (coreEvent C.val) * (coreFiberLaw C).real s =
      (Nat.card s : ℝ) / Fintype.card (FiniteWired.Recurrent N) := by
  letI := C.property
  rw [core_event_real_eq_card, coreFiberLaw, FiniteAvalanches.uniformMeasure_real_apply]
  have hc : (Nat.card (CoreField o C.val.val) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.card_pos (α := CoreField o C.val.val))
  have hd : (Fintype.card (FiniteWired.Recurrent N) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- The original-normalized omission sum is weighted by the original core masses
and actual whole-fiber held-missing probabilities, over exactly nonempty fibers. -/
theorem normalized_held_omissions_eq_core_probabilities (o : FiniteWired.Active N)
    (S : Finset Site2) :
    (∑ g : Punctured N o,
      (if S ⊆ core g.val ∧ ¬S ⊆ heldInterior g.val (coreShape g.val) then 1 else 0 : ℝ)) /
      Fintype.card (FiniteWired.Recurrent N) =
      ∑ C : PopulatedCoreShape o, if S ⊆ C.val.val then
        (puncturedCountingMeasure o).real (coreEvent C.val) *
          (coreFiberLaw C).real {g | ¬S ⊆ heldInterior g.val.val C.val}
      else 0 := by
  rw [sum_held_omissions_by_core, Finset.sum_div]
  apply Finset.sum_congr_set {C : ComponentShape o | Nonempty (CoreField o C.val)}
  · intro C hC
    by_cases hSC : S ⊆ C.val
    · rw [if_pos hSC, if_pos hSC, core_mass_mul_fiber_probability]
      congr 1
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact Finset.sum_boole _ _
    · rw [if_neg hSC, if_neg hSC, zero_div]
  · intro C hC
    letI : IsEmpty (CoreField o C.val) := not_nonempty_iff.mp hC
    simp

end
end FiniteAvalanches.Sandpile.Components
