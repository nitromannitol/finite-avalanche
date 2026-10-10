module

public import FiniteAvalanches.Sandpile.Burning.TreeHeights

@[expose] public section

/-! Natural ranks of individual original copies let global inverses compare
proved-equal candidate sets without exposing dependent proof transports. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {E : Type*} [LinearOrder E]

def copyRank (A : Finset E) (e : E) (he : e ∈ A) : ℕ :=
  ((A.orderIsoOfFin rfl).symm ⟨e, he⟩).val

theorem copy_rank_congr {A B : Finset E} (hAB : A = B) {e f : E}
    (hef : e = f) (he : e ∈ A) (hf : f ∈ B) : copyRank A e he = copyRank B f hf := by
  subst B
  subst f
  rfl

theorem copy_rank_injective (A : Finset E) (e f : E) (he : e ∈ A) (hf : f ∈ A)
    (hr : copyRank A e he = copyRank A f hf) : e = f := by
  have hi : (A.orderIsoOfFin rfl).symm ⟨e, he⟩ = (A.orderIsoOfFin rfl).symm ⟨f, hf⟩ :=
    Fin.ext hr
  have hh := (A.orderIsoOfFin rfl).symm.injective hi
  exact congrArg Subtype.val hh

variable {V : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (s : V)

theorem tree_height_rank_eq (t : (copiedTreeGraph G).SpanningTree) (v : SourceVertex s) :
    (treeHeights G s t v).val = treeBase G s t v +
      copyRank (treeParentCopies G s t v) (treeParent G s t v).val (treeParent G s t v).property := rfl

theorem global_parent_rank_reconstruct (h : SourceHeights G s)
    (hn : noForbidden G (Finset.univ.erase s) h) (v : SourceVertex s) :
    copyRank (parentCopies G s h (burnTime G s h hn v) v)
      (globalParentCopy G s h hn v).val (globalParentCopy G s h hn v).property +
      activeDegree G (Finset.univ.erase s) (burnRemainder G s h (burnTime G s h hn v)) v =
      (h v).val :=
  burning_parent_reconstruct_height G s h (burnTime G s h hn v) ⟨v, burn_time_spec G s h hn v⟩

end
end FiniteAvalanches.Sandpile.Burning
