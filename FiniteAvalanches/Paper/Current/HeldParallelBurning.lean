import FiniteAvalanches.Sandpile.Burning.HeldLayers
import FiniteAvalanches.Paper.SectionThree.HeldBurning

/-! The source's simultaneous held-burning clock has the proved held-past law. -/

namespace FiniteAvalanches.Paper.CurrentBurning
open FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory
open scoped Classical
noncomputable section

theorem parallel_held_burning {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [LinearOrder E] (G : FiniteAvalanches.Trees.Multigraph V E)
    (s : V) (hconn : ∀ x y : V, G.reaches Finset.univ x y)
    [MeasurableSpace (Finset V)] (B : Finset (Burning.SourceVertex s)) :
    letI : Nonempty V := ⟨s⟩
    letI : Nonempty G.SpanningTree := G.nonempty_spanning_tree hconn
    letI : Nonempty {h : Burning.SourceHeights G s //
      Burning.noForbidden G (Finset.univ.erase s) h} :=
        Nonempty.map (Burning.burningEquiv (Burning.originalGraph G) s).symm
          (by change Nonempty G.SpanningTree; infer_instance)
    Measure.map (fun h : {h : Burning.SourceHeights G s //
      Burning.noForbidden G (Finset.univ.erase s) h} =>
      (Burning.heldParallelRemainder G s h.val B
        (Fintype.card (Burning.SourceVertex s))).image Subtype.val)
      (FiniteAvalanches.uniformMeasure {h : Burning.SourceHeights G s //
        Burning.noForbidden G (Finset.univ.erase s) h}) =
    Measure.map (fun t : G.SpanningTree => Burning.canonicalPastUnion G s t B) G.treeLaw := by
  letI : Nonempty V := ⟨s⟩
  letI : Nonempty G.SpanningTree := G.nonempty_spanning_tree hconn
  letI : Nonempty {h : Burning.SourceHeights G s //
    Burning.noForbidden G (Finset.univ.erase s) h} :=
      Nonempty.map (Burning.burningEquiv (Burning.originalGraph G) s).symm
        (by change Nonempty G.SpanningTree; infer_instance)
  have he :
      (fun h : {h : Burning.SourceHeights G s //
          Burning.noForbidden G (Finset.univ.erase s) h} =>
        (Burning.heldParallelRemainder G s h.val B
          (Fintype.card (Burning.SourceVertex s))).image Subtype.val) =
      (fun h : {h : Burning.SourceHeights G s //
          Burning.noForbidden G (Finset.univ.erase s) h} =>
        (Burning.heldBurning G (Finset.univ.erase s) h.val B).image Subtype.val) := by
    funext h
    rw [Burning.held_parallel_final_eq]
  rw [he]
  exact FiniteAvalanches.Paper.SectionThree.held_burning G s hconn B

end
end FiniteAvalanches.Paper.CurrentBurning

#print axioms FiniteAvalanches.Sandpile.Burning.held_parallel_fixed_card
#print axioms FiniteAvalanches.Sandpile.Burning.held_parallel_final_eq
#print axioms FiniteAvalanches.Paper.SectionThree.held_burning
#print axioms FiniteAvalanches.Paper.CurrentBurning.parallel_held_burning
