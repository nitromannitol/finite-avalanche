import FiniteAvalanches.Wilson.Lattice.WiredBoxCopies
import FiniteAvalanches.Wilson.NonemptyQuotient

set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.WiredBoxCopies
open LatticeProb FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

/-- The actual larger box has no additional nonroot sites when the whole
exterior of the smaller box is among the prescribed one roots. -/
def nonrootActiveEquiv {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one) :
    {x : FiniteWired.Active N // FiniteWired.site x ∉ R.zero ∪ R.one} ≃
      {x : FiniteWired.Active M // FiniteWired.site x ∉ R.zero ∪ R.one} where
  toFun x := ⟨activeEmbedding hNM x.val,x.property⟩
  invFun x := ⟨FiniteWired.activeOfSite N (FiniteWired.site x.val) (by
    by_contra hx
    exact x.property (Or.inr (houtside _ hx))),x.property⟩
  left_inv x := Subtype.ext (FiniteWired.site_injective N rfl)
  right_inv x := Subtype.ext (FiniteWired.site_injective M rfl)

/-- Nonroot quotient vertices are exactly the actual nonroot active sites;
none is a root, without selecting or replacing any root. -/
def nonrootWiredEquiv (R : RootPair) (N : ℕ) :
    {v : FiniteWired.Vertex N // v ∉ (wiredRoots R N).val} ≃
      {x : FiniteWired.Active N // FiniteWired.site x ∉ R.zero ∪ R.one} where
  toFun v := match hv : v.val with
    | none => False.elim (v.property (hv.symm ▸ Or.inr trivial))
    | some x => ⟨x,by
        intro hx
        exact v.property (hv.symm ▸ hx)⟩
  invFun x := ⟨some x.val,x.property⟩
  left_inv v := by
    rcases v with ⟨v, hv⟩
    cases v with
    | none => exact (hv (Or.inr trivial)).elim
    | some x => rfl
  right_inv x := rfl

/-- The literal nonempty-root quotient vertex carriers of the two boxes agree.
This only transports vertices: the copied-forest equivalence still requires
its separate surviving-copy and incidence proof. -/
def quotientVertexEquiv {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one) :
    CopiedNetwork.NonemptyQuotient.Vertex (wiredRoots R N) ≃
      CopiedNetwork.NonemptyQuotient.Vertex (wiredRoots R M) :=
  Equiv.optionCongr ((nonrootWiredEquiv R N).trans
    ((nonrootActiveEquiv hNM R houtside).trans (nonrootWiredEquiv R M).symm))

@[simp] theorem quotientVertexEquiv_none {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one) :
    quotientVertexEquiv hNM R houtside none = none := rfl

end
end FiniteAvalanches.Wilson.Lattice.WiredBoxCopies
