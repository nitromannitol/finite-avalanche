import FiniteAvalanches.Sandpile.Components.Measure
import FiniteAvalanches.Trees.Measure
import Mathlib.Probability.ConditionalProbability

/-! Condition the actual punctured counting measure only on its core shape.
The original wired denominator cancels. The conditional field is represented on
its exact fiber, so restriction never needs a default value outside that shape. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Sandpile.Waves
open MeasureTheory
open scoped Classical ENNReal
noncomputable section

instance innerGraphAllowedMeasurableSpace {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) : MeasurableSpace (InnerGraphAllowed C) := ⊤
instance innerGraphAllowedMeasurableSingletonClass {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) : MeasurableSingletonClass (InnerGraphAllowed C) := ⟨fun _ => trivial⟩

/-- A populated actual shape fiber supplies both populated induced-field carriers. -/
instance innerGraphAllowedNonemptyOfCore {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) [Nonempty (CoreField o C.val)] : Nonempty (InnerGraphAllowed C) :=
  Nonempty.map (fun h => (coreGraphFieldEquiv C h).2) inferInstance
instance outerGraphAllowedNonemptyOfCore {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) [Nonempty (CoreField o C.val)] : Nonempty (OuterGraphAllowed C) :=
  Nonempty.map (fun h => (coreGraphFieldEquiv C h).1) inferInstance

/-- Conditioning the original finite measure gives uniform counting on the exact core fiber. -/
theorem core_shape_conditioning {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) [Nonempty (CoreField o C.val)] :
    Measure.map (Subtype.val : CoreField o C.val → Punctured N o)
      (FiniteAvalanches.uniformMeasure (CoreField o C.val)) =
      ProbabilityTheory.cond (puncturedCountingMeasure o) (coreEvent C) := by
  apply Measure.ext_of_singleton
  intro h
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _),
    FiniteAvalanches.uniformMeasure_apply,
    ProbabilityTheory.cond_apply (coreEvent C).toFinite.measurableSet]
  change (Nat.card {g : CoreField o C.val // g.val = h} : ℝ≥0∞) /
    Nat.card (CoreField o C.val) =
      (puncturedCountingMeasure o (coreEvent C))⁻¹ *
        puncturedCountingMeasure o (coreEvent C ∩ {h})
  by_cases hh : core h.val = C.val
  · let e : {g : CoreField o C.val // g.val = h} ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨⟨h, hh⟩, rfl⟩
        left_inv := fun g => by
          apply Subtype.ext
          exact Subtype.ext g.property.symm
        right_inv := fun _ => rfl }
    have he : coreEvent C ∩ {h} = {h} := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · exact And.right
      · intro hg; subst g; exact ⟨hh, rfl⟩
    rw [Nat.card_congr e, Nat.card_unique]
    simp only [Nat.cast_one]
    rw [he, punctured_counting_singleton, punctured_counting_apply]
    change 1 / (Nat.card (CoreField o C.val) : ℝ≥0∞) =
      ((Nat.card (CoreField o C.val) : ℝ≥0∞) /
        Fintype.card (FiniteWired.Recurrent N))⁻¹ *
          (Fintype.card (FiniteWired.Recurrent N) : ℝ≥0∞)⁻¹
    have hn : (Fintype.card (FiniteWired.Recurrent N) : ℝ≥0∞) ≠ 0 := by
      simp [Fintype.card_ne_zero]
    rw [ENNReal.inv_div (Or.inl (ENNReal.natCast_ne_top _)) (Or.inl hn)]
    simp only [div_eq_mul_inv, one_mul]
    rw [mul_comm (Fintype.card (FiniteWired.Recurrent N) : ℝ≥0∞),
      ENNReal.mul_inv_cancel_right hn (ENNReal.natCast_ne_top _)]
  · letI : IsEmpty {g : CoreField o C.val // g.val = h} :=
      ⟨fun g => hh (g.property ▸ g.val.property)⟩
    have he : coreEvent C ∩ {h} = ∅ := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hg, rfl⟩
      exact hh hg
    rw [Nat.card_of_isEmpty, Nat.cast_zero, ENNReal.zero_div, he, measure_empty, mul_zero]

/-- A specified inner field leaves exactly the literal outer-field choice. -/
def innerShapeFiberEquiv {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (r : InnerGraphAllowed C) :
    {h : CoreField o C.val // (coreGraphFieldEquiv C h).2 = r} ≃ OuterGraphAllowed C where
  toFun h := (coreGraphFieldEquiv C h.val).1
  invFun d := ⟨(coreGraphFieldEquiv C).symm (d, r), by simp⟩
  left_inv h := by
    apply Subtype.ext
    apply (coreGraphFieldEquiv C).injective
    simp only [Equiv.apply_symm_apply]
    exact Prod.ext rfl h.property.symm
  right_inv d := by simp

/-- Under shape-only conditioning, the entire induced inner field is uniform. -/
theorem core_shape_inner_uniform {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) [Nonempty (CoreField o C.val)] :
    Measure.map (fun h : CoreField o C.val => (coreGraphFieldEquiv C h).2)
      (FiniteAvalanches.uniformMeasure (CoreField o C.val)) =
      FiniteAvalanches.uniformMeasure (InnerGraphAllowed C) := by
  apply Measure.ext_of_singleton
  intro r
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _),
    FiniteAvalanches.uniformMeasure_apply, FiniteAvalanches.uniformMeasure_apply]
  change (Nat.card {h : CoreField o C.val // (coreGraphFieldEquiv C h).2 = r} : ℝ≥0∞) /
    Nat.card (CoreField o C.val) = (Nat.card ({r} : Set (InnerGraphAllowed C)) : ℝ≥0∞) /
      Nat.card (InnerGraphAllowed C)
  rw [Nat.card_congr (innerShapeFiberEquiv C r), card_core_graph_field C,
    Nat.cast_mul, Nat.card_unique (α := ({r} : Set (InnerGraphAllowed C)))]
  simp only [Nat.cast_one]
  have hd : (Nat.card (OuterGraphAllowed C) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.card_pos (α := OuterGraphAllowed C)))
  simpa only [mul_one] using ENNReal.mul_div_mul_left (c := (Nat.card (OuterGraphAllowed C) : ℝ≥0∞))
    1 (Nat.card (InnerGraphAllowed C)) hd (ENNReal.natCast_ne_top _)

end
end FiniteAvalanches.Sandpile.Components
