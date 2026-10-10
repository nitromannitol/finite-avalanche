module

public import FiniteAvalanches.Sandpile.Burning.GraphProperties

@[expose] public section

/-! Apply the graph equivalence to an actual held burn. The held inclusion is
proved by its operational stopping theorem; no proposed stopping set is supplied. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (s : V)

/-- The graph equivalence around an actual stop, deriving B inclusion before construction. -/
def actualHeldGraphFieldEquiv (h : SourceHeights G s) (B : Finset (SourceVertex s)) :=
  heldGraphFieldEquiv G s B (heldBurning G (Finset.univ.erase s) h B)
    (held_burning_largest G (Finset.univ.erase s) h B).1.1

/-- Literal graph-indexed restrictions of every allowed stable field and every held set. -/
def actualHeldGraphFields (h : {h : SourceHeights G s // noForbidden G (Finset.univ.erase s) h})
    (B : Finset (SourceVertex s)) :=
  actualHeldGraphFieldEquiv G s h.val B ⟨h.val, h.property, rfl⟩

end
end FiniteAvalanches.Sandpile.Burning
