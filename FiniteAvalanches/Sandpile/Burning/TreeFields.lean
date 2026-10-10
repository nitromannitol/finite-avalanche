module

public import FiniteAvalanches.Sandpile.Burning.TreeInverse
public import FiniteAvalanches.Sandpile.Burning.ActualFields

@[expose] public section

/-! Apply the proved global burning bijection on the literal induced complement
and held graph. This counts allowed-field fibers by actual pairs of copied trees.
It does not identify Markov recurrence or assume a held-past probability law. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [LinearOrder E]
    (G : Multigraph V E) (s : V)

/-- Restriction/reconstruction followed by the two actual original-copy burning bijections. -/
def heldGraphTreeEquiv (B A : Finset (SourceVertex s)) (hBA : B ⊆ A) :
    {h : SourceHeights G s // noForbidden G (Finset.univ.erase s) h ∧
      heldBurning G (Finset.univ.erase s) h B = A} ≃
      ((copiedTreeGraph (complementGraph G s A)).SpanningTree ×
        (copiedTreeGraph (sourceHeldGraph G s B A hBA)).SpanningTree) :=
  (heldGraphFieldEquiv G s B A hBA).trans
    (Equiv.prodCongr (burningEquiv (complementGraph G s A) (complementSink s A))
      (burningEquiv (sourceHeldGraph G s B A hBA) none))

/-- Both graph fields and the entire original field are recovered by the composed equivalence. -/
theorem held_graph_tree_reconstruct (B A : Finset (SourceVertex s)) (hBA : B ⊆ A)
    (h : {h : SourceHeights G s // noForbidden G (Finset.univ.erase s) h ∧
      heldBurning G (Finset.univ.erase s) h B = A}) :
    (heldGraphTreeEquiv G s B A hBA).symm (heldGraphTreeEquiv G s B A hBA h) = h :=
  (heldGraphTreeEquiv G s B A hBA).symm_apply_apply h

/-- A pair reconstructs a literal field whose operational burn stops at exactly A. -/
theorem held_graph_tree_exact_stop (B A : Finset (SourceVertex s)) (hBA : B ⊆ A)
    (t : (copiedTreeGraph (complementGraph G s A)).SpanningTree ×
      (copiedTreeGraph (sourceHeldGraph G s B A hBA)).SpanningTree) :
    heldBurning G (Finset.univ.erase s) ((heldGraphTreeEquiv G s B A hBA).symm t).val B = A :=
  ((heldGraphTreeEquiv G s B A hBA).symm t).property.2

/-- Actual stopping-set consumer derives the held inclusion instead of requesting it. -/
def actualHeldGraphTrees
    (h : {h : SourceHeights G s // noForbidden G (Finset.univ.erase s) h})
    (B : Finset (SourceVertex s)) :=
  heldGraphTreeEquiv G s B (heldBurning G (Finset.univ.erase s) h.val B)
    (held_burning_largest G (Finset.univ.erase s) h.val B).1.1 ⟨h.val, h.property, rfl⟩

/-- Exact deterministic cardinality of allowed-field fibers; no recurrent or uniform law premise. -/
theorem card_held_field_fiber (B A : Finset (SourceVertex s)) (hBA : B ⊆ A) :
    Nat.card {h : SourceHeights G s // noForbidden G (Finset.univ.erase s) h ∧
      heldBurning G (Finset.univ.erase s) h B = A} =
      Nat.card (copiedTreeGraph (complementGraph G s A)).SpanningTree *
        Nat.card (copiedTreeGraph (sourceHeldGraph G s B A hBA)).SpanningTree := by
  rw [Nat.card_congr (heldGraphTreeEquiv G s B A hBA), Nat.card_prod]

end
end FiniteAvalanches.Sandpile.Burning
