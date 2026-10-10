module

public import FiniteAvalanches.Sandpile.Burning.TreeInverse

@[expose] public section

/-! The proved canonical burning map returns literal original-copy trees.
Changing the edge equality implementation transports only subtype certificates;
every original edge subset is kept exactly. -/
namespace FiniteAvalanches.Trees.Multigraph
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E]

def spanningTreeDecidableEquiv (G : Multigraph V E) (d f : DecidableEq E) :
    @SpanningTree V E _ _ d G ≃ @SpanningTree V E _ _ f G where
  toFun t := ⟨t.val, by
    have he : d = f := Subsingleton.elim _ _
    cases he
    exact t.property⟩
  invFun t := ⟨t.val, by
    have he : f = d := Subsingleton.elim _ _
    cases he
    exact t.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem spanning_tree_decidable_equiv_edges (G : Multigraph V E) (d f : DecidableEq E)
    (t : @SpanningTree V E _ _ d G) :
    (G.spanningTreeDecidableEquiv d f t).val = t.val := rfl

end
end FiniteAvalanches.Trees.Multigraph

namespace FiniteAvalanches.Sandpile.Burning
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [LinearOrder E]

def canonicalBurningEquiv [dE : DecidableEq E] (G : FiniteAvalanches.Trees.Multigraph V E) (s : V) :
    {h : SourceHeights G s // noForbidden G (Finset.univ.erase s) h} ≃
      @FiniteAvalanches.Trees.Multigraph.SpanningTree V E _ _ dE G :=
  (burningEquiv G s).trans (G.spanningTreeDecidableEquiv LinearOrder.toDecidableEq dE)

end
end FiniteAvalanches.Sandpile.Burning
