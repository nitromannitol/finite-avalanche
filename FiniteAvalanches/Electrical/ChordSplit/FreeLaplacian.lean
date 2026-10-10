import FiniteAvalanches.Electrical.ChordSplit.CopiedDiagram
import FiniteAvalanches.Trees.ForestProjection.GramTransport

/-! The free Laplacian is unchanged by splitting one root and grounding both pieces. -/
set_option autoImplicit false

namespace FiniteAvalanches.Electrical.ChordSplit
open StatementGeometry Trees
open scoped Classical BigOperators Matrix
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

/-- The positive copied Laplacian, with loops cancelling and parallel IDs counted separately. -/
def copiedLaplacian (J : CopiedGraph V E) : Matrix V V ℝ :=
  fun x y => ∑ e : E,
    ((if J.left e = x then 1 else 0) - (if J.right e = x then 1 else 0)) *
      ((if J.left e = y then 1 else 0) - (if J.right e = y then 1 else 0))

theorem copiedLaplacian_eq_rootGram (G : Multigraph V E) (R : Finset V) :
    (copiedLaplacian (⟨G.left, G.right⟩ : CopiedGraph V E)).submatrix
      (fun x : {v : V // v ∉ R} => x.val) (fun x : {v : V // v ∉ R} => x.val) =
        G.rootGram R := by
  ext x y
  simp only [copiedLaplacian, Matrix.submatrix_apply, Multigraph.rootGram,
    Matrix.mul_apply, Matrix.transpose_apply, Multigraph.rootIncidence_apply]

omit [Fintype V] [Fintype E] in
/-- A free vertex has exactly its original preimage after the literal split and grounding. -/
theorem groundedSplitEndpoint_eq_free (alpha beta : V) (side : E → Bool)
    (e : E) (x : V) (v : {v : V // v ≠ alpha ∧ v ≠ beta}) :
    groundMap alpha beta (splitEndpoint alpha side x e) = Sum.inl v ↔ x = v.val := by
  by_cases ha : x = alpha
  · subst x
    simp only [splitEndpoint, dif_pos, groundMap, Sum.inr_ne_inl, false_iff]
    exact Ne.symm v.property.1
  · simp only [splitEndpoint, dif_neg ha, groundMap]
    by_cases hb : x = beta
    · subst x
      simp only [dif_pos, Sum.inr_ne_inl, false_iff]
      exact Ne.symm v.property.2
    · simp only [dif_neg hb, Sum.inl.injEq, Subtype.ext_iff]

omit [Fintype V] in
/-- Reindexing the entire free block uses the original free vertices and every original copy. -/
theorem groundedSplit_free_laplacian (J : CopiedGraph V E) (alpha beta : V)
    (side : E → Bool) :
    (copiedLaplacian (groundedSplitGraph J alpha beta side)).submatrix
      (fun v : {v : V // v ≠ alpha ∧ v ≠ beta} => Sum.inl v)
      (fun v : {v : V // v ≠ alpha ∧ v ≠ beta} => Sum.inl v) =
    (copiedLaplacian J).submatrix Subtype.val Subtype.val := by
  ext x y
  simp only [copiedLaplacian, Matrix.submatrix_apply, groundedSplitGraph, splitGraph,
    groundedSplitEndpoint_eq_free]

/-- The shared free-column enumeration is independent of the split index. -/
def originalFreeEquiv (alpha beta : V) :
    {v : V // v ≠ alpha ∧ v ≠ beta} ≃ {v : V // v ∉ ({alpha, beta} : Finset V)} where
  toFun v := ⟨v.val, by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or]
    using v.property⟩
  invFun v := ⟨v.val, by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or]
    using v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- These columns exhaust the free vertices of the grounded split, without restricting the carrier. -/
def groundedFreeEquiv (alpha beta : V) :
    {v : V // v ≠ alpha ∧ v ≠ beta} ≃
      {x : GroundedSplitVertex alpha beta //
        x ∉ ({Sum.inr false, Sum.inr true} : Finset (GroundedSplitVertex alpha beta))} where
  toFun v := ⟨Sum.inl v, by simp only [Finset.mem_insert, Finset.mem_singleton,
    Sum.inl_ne_inr, or_self, not_false_eq_true]⟩
  invFun x := match x with
    | ⟨Sum.inl v, _⟩ => v
    | ⟨Sum.inr false, h⟩ => False.elim (h (Finset.mem_insert_self _ _))
    | ⟨Sum.inr true, h⟩ => False.elim (h (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  left_inv _ := rfl
  right_inv x := by
    obtain ⟨x, hx⟩ := x
    cases x with
    | inl v => rfl
    | inr k =>
      cases k
      · exact (hx (Finset.mem_insert_self _ _)).elim
      · exact (hx (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))).elim

/-- The displayed free-block determinant is the determinant with the entire actual root set deleted. -/
theorem groundedSplit_free_det_eq_root_deleted_det (J : CopiedGraph V E)
    (alpha beta : V) (side : E → Bool) :
    ((copiedLaplacian (groundedSplitGraph J alpha beta side)).submatrix
      (fun v : {v : V // v ≠ alpha ∧ v ≠ beta} => Sum.inl v)
      (fun v : {v : V // v ≠ alpha ∧ v ≠ beta} => Sum.inl v)).det =
    ((copiedLaplacian (groundedSplitGraph J alpha beta side)).submatrix
      (fun x : {x : GroundedSplitVertex alpha beta //
        x ∉ ({Sum.inr false, Sum.inr true} : Finset (GroundedSplitVertex alpha beta))} => x.val)
      (fun x : {x : GroundedSplitVertex alpha beta //
        x ∉ ({Sum.inr false, Sum.inr true} : Finset (GroundedSplitVertex alpha beta))} => x.val)).det := by
  exact Matrix.det_submatrix_equiv_self (groundedFreeEquiv alpha beta)
    ((copiedLaplacian (groundedSplitGraph J alpha beta side)).submatrix Subtype.val Subtype.val)

/-- The actual free determinant is the whole original two-root forest count. -/
theorem groundedSplit_free_det_eq_forest_count (G : Multigraph V E) (alpha beta : V)
    (side : E → Bool) :
    ((copiedLaplacian (groundedSplitGraph (⟨G.left, G.right⟩ : CopiedGraph V E)
      alpha beta side)).submatrix
        (fun v : {v : V // v ≠ alpha ∧ v ≠ beta} => Sum.inl v)
        (fun v : {v : V // v ≠ alpha ∧ v ≠ beta} => Sum.inl v)).det =
      (Nat.card (G.RootedForest ({alpha, beta} : Set V)) : ℝ) := by
  rw [groundedSplit_free_laplacian]
  have hm : (copiedLaplacian (⟨G.left, G.right⟩ : CopiedGraph V E)).submatrix
      (fun v : {v : V // v ≠ alpha ∧ v ≠ beta} => v.val)
      (fun v : {v : V // v ≠ alpha ∧ v ≠ beta} => v.val) =
      (G.rootGram {alpha, beta}).submatrix
        (originalFreeEquiv alpha beta) (originalFreeEquiv alpha beta) := by
    rw [← copiedLaplacian_eq_rootGram]
    rfl
  rw [hm, Matrix.det_submatrix_equiv_self]
  simpa only [Finset.coe_insert, Finset.coe_singleton] using
    G.rootGram_det_eq_original_forest_count {alpha, beta}
      ⟨alpha, Finset.mem_insert_self _ _⟩

end
end FiniteAvalanches.Electrical.ChordSplit
