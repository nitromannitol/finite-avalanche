module

public import FiniteAvalanches.Sandpile.Burning.FieldPastEquiv
public import FiniteAvalanches.Trees.Measure

@[expose] public section

/-! The deterministic bijections give the held-past law under the actual finite
uniform measure on all stable no-forbidden fields. The denominator is the entire
original carrier. Markov recurrence is not redefined or supplied as a premise. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open MeasureTheory
open scoped Classical ENNReal
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [LinearOrder E]
    (G : Multigraph V E) (s : V)

instance allowedFieldMeasurableSpace : MeasurableSpace (AllowedField G s) := ⊤
instance allowedFieldMeasurableSingletonClass : MeasurableSingletonClass (AllowedField G s) :=
  ⟨fun _ => trivial⟩
instance sourceShapeMeasurableSpace : MeasurableSpace (Finset (SourceVertex s)) := ⊤
instance sourceShapeMeasurableSingletonClass : MeasurableSingletonClass (Finset (SourceVertex s)) :=
  ⟨fun _ => trivial⟩

/-- Nonemptiness of the allowed carrier is derived from an actual tree by the proved bijection. -/
instance allowedNonemptyOfTree [Nonempty (copiedTreeGraph G).SpanningTree] :
    Nonempty (AllowedField G s) :=
  Nonempty.map (burningEquiv G s).symm inferInstance

variable [Nonempty (copiedTreeGraph G).SpanningTree]

/-- Every shape, including impossible shapes, has the same normalized mass. -/
theorem uniform_held_stop_eq_past (B A : Finset (SourceVertex s)) :
    FiniteAvalanches.uniformMeasure (AllowedField G s)
      {h | heldBurning G (Finset.univ.erase s) h.val B = A} =
      (copiedTreeGraph G).treeLaw {t | sourcePastUnion G s t B = A} := by
  rw [FiniteAvalanches.uniformMeasure_apply, FiniteAvalanches.Trees.Multigraph.treeLaw,
    FiniteAvalanches.uniformMeasure_apply, card_allowed_eq_trees G s]
  change (Nat.card {h : AllowedField G s // heldBurning G (Finset.univ.erase s) h.val B = A} : ℝ≥0∞) /
    Nat.card (copiedTreeGraph G).SpanningTree =
      (Nat.card {t : (copiedTreeGraph G).SpanningTree // sourcePastUnion G s t B = A} : ℝ≥0∞) /
        Nat.card (copiedTreeGraph G).SpanningTree
  rw [card_held_stop_eq_past G s B A]

/-- Equality of the full finite laws, before any transition event is imposed. -/
theorem uniform_held_past_law (B : Finset (SourceVertex s)) :
    Measure.map (fun h : AllowedField G s => heldBurning G (Finset.univ.erase s) h.val B)
      (FiniteAvalanches.uniformMeasure (AllowedField G s)) =
      Measure.map (fun t : (copiedTreeGraph G).SpanningTree => sourcePastUnion G s t B)
        (copiedTreeGraph G).treeLaw := by
  apply Measure.ext_of_singleton
  intro A
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _),
    Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
  exact uniform_held_stop_eq_past G s B A

/-- The original-copy product is divided by the original tree count. -/
theorem uniform_held_stop_product (B A : Finset (SourceVertex s)) (hBA : B ⊆ A) :
    FiniteAvalanches.uniformMeasure (AllowedField G s)
      {h | heldBurning G (Finset.univ.erase s) h.val B = A} =
      (Nat.card (copiedTreeGraph (complementGraph G s A)).SpanningTree : ℝ≥0∞) *
        Nat.card (copiedTreeGraph (sourceHeldGraph G s B A hBA)).SpanningTree /
          Nat.card (copiedTreeGraph G).SpanningTree := by
  rw [uniform_held_stop_eq_past G s B A, FiniteAvalanches.Trees.Multigraph.treeLaw,
    FiniteAvalanches.uniformMeasure_apply]
  change (Nat.card {t : (copiedTreeGraph G).SpanningTree // sourcePastUnion G s t B = A} : ℝ≥0∞) / _ = _
  rw [Nat.card_congr (sourcePastFiberEquiv G s B A), card_held_past_fiber G s B (A.image Subtype.val) (source_shape_avoids_sink s A)
      (source_shape_subset s B A hBA), Nat.cast_mul]
  rfl

end
end FiniteAvalanches.Sandpile.Burning
