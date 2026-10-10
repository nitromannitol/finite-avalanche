module

public import FiniteAvalanches.Sandpile.Burning.Parents
public import FiniteAvalanches.Trees.CopiedEdges

@[expose] public section

/-! The canonical copied-tree graph keeps the identical vertex and original E
carriers. Actual burning parents give paths to the sink and therefore connected
selected copies, without assuming a tree or a counting identity. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E)

def copiedTreeGraph : FiniteAvalanches.Trees.Multigraph V E :=
  ⟨G.left, G.right, G.loopless⟩

variable [LinearOrder E] (s : V)

theorem parent_edge_mem (h : SourceHeights G s) (hn : noForbidden G (Finset.univ.erase s) h)
    (v : SourceVertex s) : (globalParentCopy G s h hn v).val ∈ parentEdgeSet G s h hn :=
  Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩

theorem parent_step (h : SourceHeights G s) (hn : noForbidden G (Finset.univ.erase s) h)
    (v : SourceVertex s) (w : V)
    (hw : (G.left (globalParentCopy G s h hn v).val = v.val ∧
        G.right (globalParentCopy G s h hn v).val = w) ∨
      (G.right (globalParentCopy G s h hn v).val = v.val ∧
        G.left (globalParentCopy G s h hn v).val = w)) :
    (copiedTreeGraph G).reaches (parentEdgeSet G s h hn) v.val w :=
  Relation.ReflTransGen.single ⟨(globalParentCopy G s h hn v).val, parent_edge_mem G s h hn v, hw⟩

theorem parent_reaches_sink (h : SourceHeights G s) (hn : noForbidden G (Finset.univ.erase s) h)
    (v : SourceVertex s) : (copiedTreeGraph G).reaches (parentEdgeSet G s h hn) v.val s := by
  have go : ∀ n : ℕ, ∀ x : SourceVertex s, burnTime G s h hn x = n →
      (copiedTreeGraph G).reaches (parentEdgeSet G s h hn) x.val s := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      have finish : ∀ w : V,
          ((G.left (globalParentCopy G s h hn x).val = x.val ∧
              G.right (globalParentCopy G s h hn x).val = w) ∨
            (G.right (globalParentCopy G s h hn x).val = x.val ∧
              G.left (globalParentCopy G s h hn x).val = w)) →
          (copiedTreeGraph G).reaches (parentEdgeSet G s h hn) x.val s := by
        intro w hw
        have hs := parent_step G s h hn x w hw
        rcases global_parent_previous G s h hn x w hw with he | ⟨y, he, ht⟩
        · simpa only [he] using hs
        · have hlt : burnTime G s h hn y < n := by omega
          have hy := ih (burnTime G s h hn y) hlt y rfl
          unfold FiniteAvalanches.Trees.Multigraph.reaches at hy
          rw [he] at hy
          exact hs.trans hy
      rcases global_parent_incident G s h hn x with hl | hr
      · exact finish _ (Or.inl ⟨hl.1, rfl⟩)
      · exact finish _ (Or.inr ⟨hr.1, rfl⟩)
  exact go _ v rfl

theorem parent_copies_connected (h : SourceHeights G s) (hn : noForbidden G (Finset.univ.erase s) h) :
    ∀ x y : V, (copiedTreeGraph G).reaches (parentEdgeSet G s h hn) x y := by
  have hs : ∀ x : V, (copiedTreeGraph G).reaches (parentEdgeSet G s h hn) x s := by
    intro x
    by_cases hx : x = s
    · subst x; exact Relation.ReflTransGen.refl
    · exact parent_reaches_sink G s h hn ⟨x, Finset.mem_erase.mpr ⟨hx, Finset.mem_univ _⟩⟩
  intro x y
  exact (hs x).trans ((copiedTreeGraph G).reaches_symm (hs y))

end
end FiniteAvalanches.Sandpile.Burning
