import FiniteAvalanches.Sandpile.Burning.RawHeldEncoding
import FiniteAvalanches.Paper.Current.HeldParallelBurning
import FiniteAvalanches.Probability.UniformMap

/-! Whole-field and held-past laws on the raw stable NoFSC carrier. -/
namespace FiniteAvalanches.Sandpile.RawGraph
open FiniteAvalanches.Sandpile MeasureTheory
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : FiniteAvalanches.Trees.Multigraph V E) (s : V)

instance rawAllowedFintype : Fintype (AllowedState G s) :=
  Fintype.ofEquiv _ (allowedFieldEquiv G s).symm
instance rawAllowedMeasurableSpace : MeasurableSpace (AllowedState G s) := ⊤
instance rawAllowedMeasurableSingletonClass : MeasurableSingletonClass (AllowedState G s) :=
  ⟨fun _ => trivial⟩

/-- Population is obtained from an actual tree and both proved field bijections. -/
theorem raw_allowed_nonempty_of_tree [LinearOrder E] (t : G.SpanningTree) :
    Nonempty (AllowedState G s) := by
  let h : {h : Burning.SourceHeights G s // Burning.noForbidden G (Finset.univ.erase s) h} :=
    (Burning.burningEquiv (Burning.originalGraph G) s).symm t
  exact ⟨(allowedFieldEquiv G s).symm h⟩

theorem raw_no_fsc_field_law [LinearOrder E]
    (hconn : ∀ x y : V, G.reaches Finset.univ x y) :
    letI : Nonempty V := ⟨s⟩
    letI : Nonempty G.SpanningTree := G.nonempty_spanning_tree hconn
    letI : Nonempty {h : Burning.SourceHeights G s //
      Burning.noForbidden G (Finset.univ.erase s) h} :=
      Nonempty.map (Burning.burningEquiv (Burning.originalGraph G) s).symm
        (by change Nonempty G.SpanningTree; infer_instance)
    letI : Nonempty (AllowedState G s) := Nonempty.map (allowedFieldEquiv G s).symm inferInstance
    Measure.map (allowedFieldEquiv G s) (FiniteAvalanches.uniformMeasure (AllowedState G s)) =
      FiniteAvalanches.uniformMeasure {h : Burning.SourceHeights G s //
        Burning.noForbidden G (Finset.univ.erase s) h} := by
  letI : Nonempty V := ⟨s⟩
  letI : Nonempty G.SpanningTree := G.nonempty_spanning_tree hconn
  letI : Nonempty {h : Burning.SourceHeights G s //
    Burning.noForbidden G (Finset.univ.erase s) h} :=
    Nonempty.map (Burning.burningEquiv (Burning.originalGraph G) s).symm
      (by change Nonempty G.SpanningTree; infer_instance)
  letI : Nonempty (AllowedState G s) := Nonempty.map (allowedFieldEquiv G s).symm inferInstance
  exact FiniteAvalanches.uniform_measure_map_equiv (allowedFieldEquiv G s)

/-- The pushforward is the actual signed source field, coordinate for coordinate. -/
theorem raw_no_fsc_source_field_law [LinearOrder E]
    (hconn : ∀ x y : V, G.reaches Finset.univ x y) [MeasurableSpace (Field s)] :
    letI : Nonempty V := ⟨s⟩
    letI : Nonempty G.SpanningTree := G.nonempty_spanning_tree hconn
    letI : Nonempty {h : Burning.SourceHeights G s //
      Burning.noForbidden G (Finset.univ.erase s) h} :=
      Nonempty.map (Burning.burningEquiv (Burning.originalGraph G) s).symm
        (by change Nonempty G.SpanningTree; infer_instance)
    letI : Nonempty (AllowedState G s) := Nonempty.map (allowedFieldEquiv G s).symm inferInstance
    Measure.map (fun η : AllowedState G s => η.val.val)
      (FiniteAvalanches.uniformMeasure (AllowedState G s)) =
      Measure.map (fun h : {h : Burning.SourceHeights G s //
        Burning.noForbidden G (Finset.univ.erase s) h} => fun x => ((h.val x).val : ℤ))
        (FiniteAvalanches.uniformMeasure {h : Burning.SourceHeights G s //
          Burning.noForbidden G (Finset.univ.erase s) h}) := by
  letI : Nonempty V := ⟨s⟩
  letI : Nonempty G.SpanningTree := G.nonempty_spanning_tree hconn
  letI : Nonempty {h : Burning.SourceHeights G s //
    Burning.noForbidden G (Finset.univ.erase s) h} :=
    Nonempty.map (Burning.burningEquiv (Burning.originalGraph G) s).symm
      (by change Nonempty G.SpanningTree; infer_instance)
  letI : Nonempty (AllowedState G s) := Nonempty.map (allowedFieldEquiv G s).symm inferInstance
  have he : (fun η : AllowedState G s => η.val.val) =
      (fun h : {h : Burning.SourceHeights G s //
        Burning.noForbidden G (Finset.univ.erase s) h} => fun x => ((h.val x).val : ℤ)) ∘
        allowedFieldEquiv G s := by
    funext η x
    exact (source_field_encoding_value G s η x).symm
  rw [he, ← Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
    raw_no_fsc_field_law G s hconn]

/-- This is a NoFSC law. Its identification with source accessibility recurrence
requires the separate generic criterion, never an extra premise of the clock. -/
theorem raw_no_fsc_held_past_law [LinearOrder E]
    (hconn : ∀ x y : V, G.reaches Finset.univ x y)
    [MeasurableSpace (Finset V)] (B : Finset (Burning.SourceVertex s)) :
    letI : Nonempty V := ⟨s⟩
    letI : Nonempty G.SpanningTree := G.nonempty_spanning_tree hconn
    letI : Nonempty {h : Burning.SourceHeights G s //
      Burning.noForbidden G (Finset.univ.erase s) h} :=
      Nonempty.map (Burning.burningEquiv (Burning.originalGraph G) s).symm
        (by change Nonempty G.SpanningTree; infer_instance)
    letI : Nonempty (AllowedState G s) := Nonempty.map (allowedFieldEquiv G s).symm inferInstance
    Measure.map (fun η : AllowedState G s => (sourceHeldBurning G s η.val B).image Subtype.val)
      (FiniteAvalanches.uniformMeasure (AllowedState G s)) =
      Measure.map (fun t : G.SpanningTree => Burning.canonicalPastUnion G s t B) G.treeLaw := by
  letI : Nonempty V := ⟨s⟩
  letI : Nonempty G.SpanningTree := G.nonempty_spanning_tree hconn
  letI : Nonempty {h : Burning.SourceHeights G s //
    Burning.noForbidden G (Finset.univ.erase s) h} :=
    Nonempty.map (Burning.burningEquiv (Burning.originalGraph G) s).symm
      (by change Nonempty G.SpanningTree; infer_instance)
  letI : Nonempty (AllowedState G s) := Nonempty.map (allowedFieldEquiv G s).symm inferInstance
  let observable (h : {h : Burning.SourceHeights G s //
      Burning.noForbidden G (Finset.univ.erase s) h}) :=
    (Burning.heldParallelRemainder G s h.val B
      (Fintype.card (Burning.SourceVertex s))).image Subtype.val
  have he : (fun η : AllowedState G s => (sourceHeldBurning G s η.val B).image Subtype.val) =
      observable ∘ allowedFieldEquiv G s := by
    funext η
    exact congrArg (fun A => A.image Subtype.val)
      (source_clock_encoding G s η B (Fintype.card (Burning.SourceVertex s)))
  rw [he, ← Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
    raw_no_fsc_field_law G s hconn]
  exact FiniteAvalanches.Paper.CurrentBurning.parallel_held_burning G s hconn B

end
end FiniteAvalanches.Sandpile.RawGraph
