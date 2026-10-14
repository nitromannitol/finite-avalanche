import FiniteAvalanches.Sandpile.Recurrence.RawGraphAccessibility
import FiniteAvalanches.Sandpile.Recurrence.RawGraphHeldBurning
import FiniteAvalanches.Sandpile.Burning.PastVertexLaw
import FiniteAvalanches.Probability.UniformMap

/-! Actual accessibility recurrent raw fields, their unique finite height
encoding, uniform count, and held-past law on the original copied graph. -/
namespace FiniteAvalanches.Sandpile.RawGraph
open FiniteAvalanches.Sandpile
open MeasureTheory
open scoped Classical ENNReal
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : FiniteAvalanches.Trees.Multigraph V E) (s : V)

/-- An auxiliary ordering is derived from finiteness, never assumed as source data. -/
local instance chosenEdgeOrder : LinearOrder E :=
  LinearOrder.lift' (Fintype.equivFin E) (Fintype.equivFin E).injective

/-- Every later source round retains the actual finite terminal set. -/
theorem held_parallel_after_card (η : Field s) (B : Finset (Burning.SourceVertex s))
    (n : ℕ) : heldParallelRemainder G s η B (Fintype.card (Burning.SourceVertex s) + n) =
      heldBurning G s η B := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.add_succ, heldParallelRemainder, ih]
    exact held_parallel_fixed_card G s η B

abbrev Connected := (FiniteAvalanches.Electrical.supportGraph G.left G.right).Preconnected

noncomputable abbrev recurrentFintype (hc : Connected G) : Fintype (RecurrentState G s) :=
  Fintype.ofEquiv (Burning.AllowedField G s) (recurrentFieldEquiv G s hc).symm

abbrev recurrentNonempty (hc : Connected G) : Nonempty (RecurrentState G s) :=
  ⟨⟨⟨maximalStable G s, maximal_stable G s⟩,
    no_fsc_accessible G s hc (maximal_no_fsc G s hc)⟩⟩

abbrev treeNonempty (hc : Connected G) : Nonempty (Burning.copiedTreeGraph G).SpanningTree :=
  Nonempty.map ((recurrentFieldEquiv G s hc).trans (Burning.burningEquiv G s))
    (recurrentNonempty G s hc)

instance recurrentMeasurableSpace : MeasurableSpace (RecurrentState G s) := ⊤
instance recurrentMeasurableSingletonClass : MeasurableSingletonClass (RecurrentState G s) :=
  ⟨fun _ => trivial⟩

/-- Uniform measure on stable raw fields accessible from EVERY raw field. -/
def recurrentLaw (hc : Connected G) : Measure (RecurrentState G s) := by
  letI := recurrentFintype G s hc
  letI := recurrentNonempty G s hc
  exact FiniteAvalanches.uniformMeasure (RecurrentState G s)

/-- Uniform law on the literal copied-tree carrier, with nonemptiness proved from connectivity. -/
def copiedTreeLaw (hc : Connected G) : Measure (Burning.copiedTreeGraph G).SpanningTree := by
  letI := treeNonempty G s hc
  exact (Burning.copiedTreeGraph G).treeLaw

theorem recurrent_encoding_value (hc : Connected G) (η : RecurrentState G s)
    (x : Burning.SourceVertex s) :
    (((recurrentFieldEquiv G s hc η).val x).val : ℤ) = η.val.val x :=
  bounded_heights_value G s (recurrentAllowedEquiv G s hc η) x

theorem recurrent_encoding_unique (hc : Connected G) (η : RecurrentState G s)
    (f : Burning.SourceHeights G s) (hf : ∀ x, ((f x).val : ℤ) = η.val.val x) :
    f = (recurrentFieldEquiv G s hc η).val :=
  bounded_heights_unique G s (recurrentAllowedEquiv G s hc η) f hf

/-- Exact count now applies to the accessibility carrier, using the proven characterization. -/
theorem card_recurrent_eq_trees (hc : Connected G) :
    Nat.card (RecurrentState G s) = Nat.card (Burning.copiedTreeGraph G).SpanningTree :=
  Nat.card_congr ((recurrentFieldEquiv G s hc).trans (Burning.burningEquiv G s))

/-- The full carrier law, before a held event is selected. -/
theorem recurrent_law_encoding (hc : Connected G) :
    Measure.map (recurrentFieldEquiv G s hc) (recurrentLaw G s hc) =
      letI := treeNonempty G s hc
      FiniteAvalanches.uniformMeasure (Burning.AllowedField G s) := by
  letI := recurrentFintype G s hc
  letI := recurrentNonempty G s hc
  letI := treeNonempty G s hc
  exact FiniteAvalanches.uniform_measure_map_equiv (recurrentFieldEquiv G s hc)

/-- Operational held burning after the unique, value-preserving Fin(degree) encoding. -/
def heldStop (B : Finset (Burning.SourceVertex s))
    (η : RecurrentState G s) : Finset (Burning.SourceVertex s) :=
  heldBurning G s η.val.val B

theorem held_stop_encoding (hc : Connected G) (B : Finset (Burning.SourceVertex s))
    (η : RecurrentState G s) : heldStop G s B η =
      Burning.heldBurning G (Finset.univ.erase s) (recurrentFieldEquiv G s hc η).val B :=
  held_burning_encoding G s η.val.val _ (recurrent_encoding_value G s hc η) B

/-- Full law on actual original vertices; held roots are arbitrary and include the empty set. -/
theorem recurrent_held_past_law (hc : Connected G) (B : Finset (Burning.SourceVertex s))
    [MeasurableSpace (Finset V)] :
    Measure.map (fun η : RecurrentState G s => (heldStop G s B η).image Subtype.val)
      (recurrentLaw G s hc) =
      Measure.map (fun t : (Burning.copiedTreeGraph G).SpanningTree =>
        Burning.treePastUnion G s t B) (copiedTreeLaw G s hc) := by
  letI := recurrentFintype G s hc
  letI := treeNonempty G s hc
  have hm := congrArg (Measure.map (fun h : Burning.AllowedField G s =>
    (Burning.heldBurning G (Finset.univ.erase s) h.val B).image Subtype.val))
      (recurrent_law_encoding G s hc)
  rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)] at hm
  simp_rw [held_stop_encoding G s hc B]
  change _ = Measure.map (fun t : (Burning.copiedTreeGraph G).SpanningTree =>
    Burning.treePastUnion G s t B) (Burning.copiedTreeGraph G).treeLaw
  simpa only [Function.comp_def] using
    hm.trans (Burning.uniform_held_past_vertex_law G s B)

end
end FiniteAvalanches.Sandpile.RawGraph
