module

public import FiniteAvalanches.Sandpile.Burning.DegreeTransport

@[expose] public section

/-! Forbidden-subconfiguration tests on the actual induced and held copied
multigraphs. Stability uses their own degrees, including degree zero. Each subset
degree is transported by the identity of original edge copies, not a tree law. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E)

def inducedAllowed (C : Finset V)
    (h : (v : InducedVertex C) → Fin (degree (inducedGraph G C) v)) : Prop :=
  ∀ S : Finset (InducedVertex C),
    ¬(S.Nonempty ∧ ∀ v ∈ S, (h v).val < degreeInto (inducedGraph G C) S v)

theorem induced_allowed_iff (C : Finset V)
    (h : (v : InducedVertex C) → Fin (degree (inducedGraph G C) v)) :
    inducedAllowed G C h ↔ ∀ S : Finset (InducedVertex C),
      ¬(S.Nonempty ∧ ∀ v ∈ S, (h v).val < degreeInto G (S.image Subtype.val) v.val) := by
  simp only [inducedAllowed, degree_into_induced_graph]

def heldAllowed (s : V) (A B : Finset V) (hs : s ∉ A) (hBA : B ⊆ A)
    (h : (v : InducedVertex A) → Fin (degree (heldGraph G s A B hs hBA) (some v))) : Prop :=
  ∀ S : Finset (InducedVertex A), ¬(S.Nonempty ∧ ∀ v ∈ S,
    (h v).val < degreeInto (heldGraph G s A B hs hBA) (S.image some) (some v))

theorem held_allowed_iff (s : V) (A B : Finset V) (hs : s ∉ A) (hBA : B ⊆ A)
    (h : (v : InducedVertex A) → Fin (degree (heldGraph G s A B hs hBA) (some v))) :
    heldAllowed G s A B hs hBA h ↔ ∀ S : Finset (InducedVertex A),
      ¬(S.Nonempty ∧ ∀ v ∈ S, (h v).val < degreeInto G (S.image Subtype.val) v.val) := by
  simp only [heldAllowed, degree_into_held_graph]

theorem degree_induced_compl (A : Finset V) (v : InducedVertex (Finset.univ \ A)) :
    degree (inducedGraph G (Finset.univ \ A)) v = degree G v.val - degreeInto G A v.val := by
  rw [degree_induced_graph]
  have hd := degree_into_compl G A v.val
  omega

end
end FiniteAvalanches.Sandpile.Burning
