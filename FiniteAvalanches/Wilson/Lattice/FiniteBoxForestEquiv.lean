import FiniteAvalanches.Wilson.Lattice.QuotientCopyIncidence
import FiniteAvalanches.Trees.CopiedTreeTransport

/-! Ordinary cross-volume equivalence on the existing copied rooted forests.
All roots outside the small box are actual one roots; no distributional
identity, forest equivalence, or component-color conclusion is a premise. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.WiredBoxCopies
open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open CopiedNetwork.NonemptyQuotient
open scoped Classical
noncomputable section

def quotientTreeEquiv {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one) :
    (graph (WiredTrees.graph N) (wiredRoots R N)).ComponentTree Set.univ ≃
      (graph (WiredTrees.graph M) (wiredRoots R M)).ComponentTree Set.univ where
  toFun t := ⟨t.val.image (quotientCopyEquiv hNM R houtside),
    (Multigraph.copiedEquiv_tree_iff _ _ (quotientVertexEquiv hNM R houtside)
      (quotientCopyEquiv hNM R houtside) (quotientCopyEquiv_endpoints hNM R houtside)
      t.val).mpr t.property⟩
  invFun t := ⟨t.val.image (quotientCopyEquiv hNM R houtside).symm,by
    apply (Multigraph.copiedEquiv_tree_iff _ _ (quotientVertexEquiv hNM R houtside)
      (quotientCopyEquiv hNM R houtside) (quotientCopyEquiv_endpoints hNM R houtside)
      _).mp
    simpa only [Finset.image_image,Function.comp_def,Equiv.apply_symm_apply,
      Finset.image_id'] using t.property⟩
  left_inv t := by
    apply Subtype.ext
    simp only [Finset.image_image,Function.comp_def,Equiv.symm_apply_apply,
      Finset.image_id']
  right_inv t := by
    apply Subtype.ext
    simp only [Finset.image_image,Function.comp_def,Equiv.apply_symm_apply,
      Finset.image_id']

theorem liftCopies_image_quotientCopyEquiv {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one)
    (t : Finset (Copy (WiredTrees.graph N) (wiredRoots R N))) :
    liftCopies (WiredTrees.graph M) (wiredRoots R M)
        (t.image (quotientCopyEquiv hNM R houtside)) =
      (liftCopies (WiredTrees.graph N) (wiredRoots R N) t).image (copyInLarger hNM) := by
  change (t.image (quotientCopyEquiv hNM R houtside)).image Subtype.val =
    (t.image Subtype.val).image (copyInLarger hNM)
  rw [Finset.image_image,Finset.image_image]
  rfl

/-- Genuine bijection of the whole existing forest carriers. -/
def finiteForestEquiv {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one) :
    FiniteForest R N ≃ FiniteForest R M :=
  (rootContractionEquiv (WiredTrees.graph N) (wiredRoots R N)).trans
    ((quotientTreeEquiv hNM R houtside).trans
      (rootContractionEquiv (WiredTrees.graph M) (wiredRoots R M)).symm)

@[simp] theorem finiteForestEquiv_copies {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one) (F : FiniteForest R N) :
    (finiteForestEquiv hNM R houtside F).val = F.val.image (copyInLarger hNM) := by
  change liftCopies (WiredTrees.graph M) (wiredRoots R M)
      ((projectCopies (WiredTrees.graph N) (wiredRoots R N) F.val).image
        (quotientCopyEquiv hNM R houtside)) = _
  rw [liftCopies_image_quotientCopyEquiv,lift_project_forest _ _ F.property]

@[simp] theorem finiteForestEquiv_symm_copies {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one) (F : FiniteForest R M) :
    ((finiteForestEquiv hNM R houtside).symm F).val = restrictCopies hNM F.val := by
  apply Finset.image_injective (copyInLarger_injective hNM)
  rw [image_restrictCopies_forest hNM R houtside F,
    ← finiteForestEquiv_copies hNM R houtside]
  exact congrArg Subtype.val ((finiteForestEquiv hNM R houtside).apply_symm_apply F)

/-- Whole original-copy counts agree, with no exterior-root multiplicity factor. -/
theorem finiteForestCount_eq {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one) :
    finiteForestCount R N = finiteForestCount R M :=
  Nat.card_congr (finiteForestEquiv hNM R houtside)

end
end FiniteAvalanches.Wilson.Lattice.WiredBoxCopies
