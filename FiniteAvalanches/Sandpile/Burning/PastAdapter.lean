module

public import FiniteAvalanches.Sandpile.Burning.PastVertexLaw
public import FiniteAvalanches.Sandpile.Burning.SourceFields

@[expose] public section

/-! A literal endpoint adapter consumes actual canonical graph-indexed fields.
All copies and vertices are unchanged. Its three body identities are definitional,
so the proved law applies to the canonical stable/no-forbidden/burning observables. -/
namespace FiniteAvalanches.Sandpile.Burning
open MeasureTheory
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [LinearOrder E]
    (G : FiniteAvalanches.Trees.Multigraph V E) (s : V)

/-- Same full vertex carrier, same original copy IDs, same endpoint maps. -/
def originalGraph : FiniteAvalanches.Trees.Multigraph V E :=
  ⟨G.left, G.right, G.loopless⟩

omit [DecidableEq V] [LinearOrder E] in
theorem original_graph_tree_body : copiedTreeGraph (originalGraph G) = G := rfl

omit [LinearOrder E] in
theorem canonical_source_heights_body :
    SourceHeights (originalGraph G) s = Burning.SourceHeights G s := rfl

omit [LinearOrder E] in
theorem canonical_no_forbidden_body (h : Burning.SourceHeights G s) :
    noForbidden (originalGraph G) (Finset.univ.erase s) h ↔
      Burning.noForbidden G (Finset.univ.erase s) h := Iff.rfl

omit [LinearOrder E] in
theorem canonical_held_burning_body (h : Burning.SourceHeights G s)
    (B : Finset (Burning.SourceVertex s)) :
    heldBurning (originalGraph G) (Finset.univ.erase s) h B =
      Burning.heldBurning G (Finset.univ.erase s) h B := by
  exact Finset.Subset.antisymm
    ((Burning.held_burning_largest G (Finset.univ.erase s) h B).2 _
      (held_burning_largest (originalGraph G) (Finset.univ.erase s) h B).1)
    ((held_burning_largest (originalGraph G) (Finset.univ.erase s) h B).2 _
      (Burning.held_burning_largest G (Finset.univ.erase s) h B).1)

/-- The canonical observable is the literal union of the actual outgoing-edge pasts. -/
def canonicalPastUnion (t : G.SpanningTree) (B : Finset (Burning.SourceVertex s)) : Finset V :=
  Finset.univ.filter fun x => ∃ b ∈ B, x ∈ G.past t s b.val (Burning.source_vertex_ne_sink s b)

theorem canonical_past_union_body (t : G.SpanningTree) (B : Finset (Burning.SourceVertex s)) :
    canonicalPastUnion G s t B = treePastUnion (originalGraph G) s t B := rfl

local instance canonicalAllowedMeasurableSpace : MeasurableSpace
    {h : Burning.SourceHeights G s // Burning.noForbidden G (Finset.univ.erase s) h} := ⊤
local instance canonicalAllowedMeasurableSingletonClass : MeasurableSingletonClass
    {h : Burning.SourceHeights G s // Burning.noForbidden G (Finset.univ.erase s) h} := ⟨fun _ => trivial⟩
local instance canonicalAllowedNonempty [Nonempty G.SpanningTree] : Nonempty
    {h : Burning.SourceHeights G s // Burning.noForbidden G (Finset.univ.erase s) h} :=
  Nonempty.map (burningEquiv (originalGraph G) s).symm
    (by change Nonempty G.SpanningTree; infer_instance)

/-- The full held-past law on the actual canonical field and original tree carriers. -/
theorem canonical_uniform_held_past_law [Nonempty G.SpanningTree]
    [MeasurableSpace (Finset V)] (B : Finset (Burning.SourceVertex s)) :
    Measure.map (fun h : {h : Burning.SourceHeights G s //
        Burning.noForbidden G (Finset.univ.erase s) h} =>
      (Burning.heldBurning G (Finset.univ.erase s) h.val B).image Subtype.val)
      (FiniteAvalanches.uniformMeasure {h : Burning.SourceHeights G s //
        Burning.noForbidden G (Finset.univ.erase s) h}) =
      Measure.map (fun t : G.SpanningTree => canonicalPastUnion G s t B) G.treeLaw := by
  letI : Nonempty (copiedTreeGraph (originalGraph G)).SpanningTree := by
    change Nonempty G.SpanningTree
    infer_instance
  have h := uniform_held_past_vertex_law (originalGraph G) s B
  rw [show (fun h : AllowedField (originalGraph G) s =>
    (heldBurning (originalGraph G) (Finset.univ.erase s) h.val B).image Subtype.val) =
      (fun h : AllowedField (originalGraph G) s =>
        (Burning.heldBurning G (Finset.univ.erase s) h.val B).image Subtype.val) by
          funext h
          rw [canonical_held_burning_body]] at h
  convert h using 1 <;> rfl

end
end FiniteAvalanches.Sandpile.Burning
