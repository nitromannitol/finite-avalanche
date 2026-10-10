module

public import FiniteAvalanches.Sandpile.Burning.PastLaw

@[expose] public section

/-! Translate the subtype law to the literal full vertex carrier. The tree
observable is its actual union of pasts, not a substituted event or carrier. -/
namespace FiniteAvalanches.Sandpile.Burning
open MeasureTheory
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [LinearOrder E]
    (G : FiniteAvalanches.Trees.Multigraph V E) (s : V)
    [Nonempty (copiedTreeGraph G).SpanningTree]
    [MeasurableSpace (Finset V)]

/-- The full source-observable law, with the complete original vertex carrier. -/
theorem uniform_held_past_vertex_law (B : Finset (SourceVertex s)) :
    Measure.map (fun h : AllowedField G s =>
      (heldBurning G (Finset.univ.erase s) h.val B).image Subtype.val)
      (FiniteAvalanches.uniformMeasure (AllowedField G s)) =
      Measure.map (fun t : (copiedTreeGraph G).SpanningTree => treePastUnion G s t B)
        (copiedTreeGraph G).treeLaw := by
  have h := congrArg (Measure.map (fun A : Finset (SourceVertex s) => A.image Subtype.val))
    (uniform_held_past_law G s B)
  rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
    Measure.map_map (measurable_of_finite _) (measurable_of_finite _)] at h
  simpa only [Function.comp_def, source_past_union_image] using h

end
end FiniteAvalanches.Sandpile.Burning
