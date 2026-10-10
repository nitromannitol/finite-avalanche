import FiniteAvalanches.Trees.Lattice.TreeContinuityObjects
import FiniteAvalanches.Sandpile.Components.Incident
import FiniteAvalanches.Wilson.Lattice.WiredForestLaw

/-! Ordinary original-copy maps needed by finite absorbing-box restriction.
This file asserts no Wilson-law or cross-volume forest equivalence. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.WiredBoxCopies
open LatticeProb FiniteAvalanches.Trees FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

 theorem inBox_mono {N M : ℕ} (hNM : N ≤ M) {x : Site 2}
    (hx : FiniteWired.inBox N x) : FiniteWired.inBox M x := by
  intro i
  have h : (N : ℤ) ≤ M := by exact_mod_cast hNM
  obtain ⟨hl,hu⟩ := hx i
  constructor <;> omega

/-- The embedding changes only coordinate-bound certificates. -/
def activeEmbedding {N M : ℕ} (hNM : N ≤ M) :
    FiniteWired.Active N ↪ FiniteWired.Active M where
  toFun x := FiniteWired.activeOfSite M (FiniteWired.site x)
    (inBox_mono hNM (fun i => (x i).property))
  inj' _ _ h := FiniteWired.site_injective N
    (congrArg (FiniteWired.site (N := M)) h)

@[simp] theorem site_activeEmbedding {N M : ℕ} (hNM : N ≤ M)
    (x : FiniteWired.Active N) :
    FiniteWired.site (activeEmbedding hNM x) = FiniteWired.site x := rfl

/-- All original copies, including individual exits, have distinct lattice IDs. -/
theorem originalCopyEdge_injective (N : ℕ) :
    Function.Injective (@TreeMeasurability11.originalCopyEdge N) := by
  intro e f he
  cases e with
  | inl e =>
    cases f with
    | inl f => exact congrArg Sum.inl (interiorEdge_injective N he)
    | inr f =>
      have hs := congrArg Subtype.val he
      rcases Sym2.eq_iff.mp hs with hs | hs
      · exact False.elim (f.property (hs.2.symm ▸ fun i => (e.val.2 i).property))
      · exact False.elim (f.property (hs.1.symm ▸ fun i => (e.val.1 i).property))
  | inr e =>
    cases f with
    | inl f =>
      have hs := congrArg Subtype.val he
      rcases Sym2.eq_iff.mp hs with hs | hs
      · exact False.elim (e.property (hs.2 ▸ fun i => (f.val.2 i).property))
      · exact False.elim (e.property (hs.2 ▸ fun i => (f.val.1 i).property))
    | inr f =>
      have hs := congrArg Subtype.val he
      rcases Sym2.eq_iff.mp hs with hs | hs
      · have hx := FiniteWired.site_injective N hs.1
        have hd : e.val.2 = f.val.2 := by
          apply FiniteWired.step_injective
          exact add_left_cancel (hs.1 ▸ hs.2)
        exact congrArg Sum.inr (Subtype.ext (Prod.ext hx hd))
      · exact False.elim (e.property (hs.2 ▸ fun i => (f.val.1 i).property))

/-- Direction copies retain the actual outside endpoint before contraction. -/
theorem originalCopyEdge_direction {N : ℕ} (x : FiniteWired.Active N)
    (d : FiniteWired.Direction) :
    (TreeMeasurability11.originalCopyEdge (FiniteWired.directionEdge x d)).val =
      s(FiniteWired.site x, FiniteWired.site x + FiniteWired.step d) := by
  rcases d with ⟨i,b⟩
  cases b
  · simp only [FiniteWired.directionEdge]
    split_ifs
    · exact Sym2.eq_swap
    · rfl
  · simp only [FiniteWired.directionEdge]
    split_ifs <;> rfl

/-- An exit in the small box becomes its same directional copy in the large
box. Its large-box representative may be internal, so no sink-exit is dropped. -/
def copyInLarger {N M : ℕ} (hNM : N ≤ M) : FiniteWired.Edge N → FiniteWired.Edge M
  | .inl e => .inl ⟨(activeEmbedding hNM e.val.1,activeEmbedding hNM e.val.2),
      by simpa only [site_activeEmbedding] using e.property⟩
  | .inr e => FiniteWired.directionEdge (activeEmbedding hNM e.val.1) e.val.2

 theorem copyInLarger_original {N M : ℕ} (hNM : N ≤ M) (e : FiniteWired.Edge N) :
    TreeMeasurability11.originalCopyEdge (copyInLarger hNM e) =
      TreeMeasurability11.originalCopyEdge e := by
  apply Subtype.ext
  cases e with
  | inl e => rfl
  | inr e => exact originalCopyEdge_direction _ _

 theorem copyInLarger_injective {N M : ℕ} (hNM : N ≤ M) :
    Function.Injective (copyInLarger hNM) := by
  intro e f he
  apply originalCopyEdge_injective N
  rw [← copyInLarger_original hNM e, ← copyInLarger_original hNM f, he]

/-- Source exterior roots force every nonroot of the large wired graph into
 the original small box; this is proved from literal root membership. -/
theorem nonroot_inside {N M : ℕ} (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one)
    (v : FiniteWired.Vertex M) (hv : v ∉ (wiredRoots R M).val) :
    ∃ x : FiniteWired.Active M, v = some x ∧ FiniteWired.inBox N (FiniteWired.site x) := by
  cases v with
  | none => exact (hv (Or.inr trivial)).elim
  | some x =>
    refine ⟨x,rfl,?_⟩
    by_contra hx
    exact hv (Or.inr (houtside _ hx))

/-- An edge between two original roots is absent from every actual rooted
forest. In particular all copies entirely exterior to the small box vanish. -/
theorem exterior_root_copies_absent {N M : ℕ} (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one)
    (F : FiniteForest R M) (e : FiniteWired.Edge M)
    (hl : (FiniteWired.endpoints e).1 = none ∨
      ∃ x, (FiniteWired.endpoints e).1 = some x ∧ ¬FiniteWired.inBox N (FiniteWired.site x))
    (hr : (FiniteWired.endpoints e).2 = none ∨
      ∃ x, (FiniteWired.endpoints e).2 = some x ∧ ¬FiniteWired.inBox N (FiniteWired.site x)) :
    e ∉ F.val := by
  have ho (v : FiniteWired.Vertex M) (h : v = none ∨
      ∃ x, v = some x ∧ ¬FiniteWired.inBox N (FiniteWired.site x)) : v ∈ wiredOne R M := by
    rcases h with rfl | ⟨x,rfl,hx⟩
    · trivial
    · exact houtside _ hx
  intro he
  obtain ⟨r,_,_,hu⟩ := F.property.2 ((WiredTrees.graph M).left e)
  have ha := hu ((WiredTrees.graph M).left e) (Or.inr (ho _ hl)) .refl
  have hb := hu ((WiredTrees.graph M).right e) (Or.inr (ho _ hr))
    (.single ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩)
  exact (WiredTrees.graph M).loopless e (ha.trans hb.symm)

end
end FiniteAvalanches.Wilson.Lattice.WiredBoxCopies
