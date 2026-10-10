import FiniteAvalanches.Electrical.Trees.LoopTransport
import FiniteAvalanches.Electrical.Trees.SeparatingForestCompletion
import FiniteAvalanches.Electrical.ChordSplit.FreeLaplacian

/-! Principal all-minors counts on copied graphs with their loop IDs retained. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
open ChordSplit Trees
open scoped Classical BigOperators
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

local instance copiedMinorNonloopDec (J : CopiedGraph V E) :
    DecidableEq {e : E // J.left e ≠ J.right e} := Classical.decEq _

/-- A loop contributes zero, so restricting the sum deletes no energy or Laplacian term. -/
theorem copiedLaplacian_nonloop (J : CopiedGraph V E) :
    copiedLaplacian J = copiedLaplacian
      (⟨J.nonloopGraph.left, J.nonloopGraph.right⟩ : CopiedGraph V _) := by
  ext x y
  let p := fun e : E => J.left e ≠ J.right e
  let f : E → ℝ := fun e : E =>
    ((if J.left e = x then 1 else 0) - (if J.right e = x then 1 else 0)) *
      ((if J.left e = y then 1 else 0) - (if J.right e = y then 1 else 0))
  change (∑ e : E, f e) = ∑ e : {e : E // p e}, f e.val
  calc
    _ = ∑ e : E, if p e then f e else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : p e
      · rw [if_pos he]
      · rw [if_neg he]
        have hloop : J.left e = J.right e := not_ne_iff.mp he
        simp only [f, hloop, sub_self, zero_mul]
    _ = ∑ e ∈ Finset.univ.filter p, f e := (Finset.sum_filter p f).symm
    _ = _ := Finset.sum_subtype (p := p) (Finset.univ.filter p) (by simp) f

/-- The copied principal Laplacian is exactly the nonloop root Gram matrix. -/
theorem copiedLaplacian_rootGram (J : CopiedGraph V E) (R : Finset V) :
    (copiedLaplacian J).submatrix
      (fun v : {v : V // v ∉ R} => v.val)
      (fun v : {v : V // v ∉ R} => v.val) = J.nonloopGraph.rootGram R := by
  rw [copiedLaplacian_nonloop]
  exact copiedLaplacian_eq_rootGram J.nonloopGraph R

/-- All-minors counts the entire copied rooted-forest carrier, with no selectable loop lost. -/
theorem copiedLaplacian_det_eq_rooted_forest_count (J : CopiedGraph V E)
    (R : Finset V) (hR : R.Nonempty) :
    ((copiedLaplacian J).submatrix
      (fun v : {v : V // v ∉ R} => v.val)
      (fun v : {v : V // v ∉ R} => v.val)).det =
        (Nat.card (J.RootedForest (R : Set V)) : ℝ) := by
  rw [copiedLaplacian_rootGram, J.nonloopGraph.rootGram_det_eq_original_forest_count R hR]
  exact_mod_cast (Nat.card_congr (J.nonloopRootedForestEquiv (R : Set V))).symm

/-- Rooting a tree at one vertex changes no selected edge subset. -/
def singletonRootedForestTreeEquiv (J : CopiedGraph V E) (u : V) :
    J.RootedForest {u} ≃ J.SpanningTree where
  toFun F := ⟨F.val, ⟨u, Set.mem_univ _⟩, by
    intro x y
    obtain ⟨r, hr, hx, _⟩ := F.property.2 x
    obtain ⟨s, hs, hy, _⟩ := F.property.2 y
    have hr' : r = u := hr
    have hs' : s = u := hs
    rw [hr'] at hx
    rw [hs'] at hy
    exact hx.trans (TwoCopy.reaches_symm J hy), F.property.1⟩
  invFun T := ⟨T.val, T.property.2.2, by
    intro x
    exact ⟨u, rfl, T.property.2.1 x u, fun _ hr _ => hr⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A one-root principal minor counts all copied spanning trees. -/
theorem copiedLaplacian_det_eq_tree_count (J : CopiedGraph V E) (u : V) :
    ((copiedLaplacian J).submatrix
      (fun v : {v : V // v ∉ ({u} : Finset V)} => v.val)
      (fun v : {v : V // v ∉ ({u} : Finset V)} => v.val)).det =
        (Nat.card J.SpanningTree : ℝ) := by
  rw [copiedLaplacian_det_eq_rooted_forest_count J {u} (Finset.singleton_nonempty u),
    Finset.coe_singleton, Nat.card_congr (singletonRootedForestTreeEquiv J u)]

/-- A two-root principal minor counts every original separating copied two-forest. -/
theorem copiedLaplacian_det_eq_twoRootForest_count (J : CopiedGraph V E) (u v : V) :
    ((copiedLaplacian J).submatrix
      (fun x : {x : V // x ∉ ({u, v} : Finset V)} => x.val)
      (fun x : {x : V // x ∉ ({u, v} : Finset V)} => x.val)).det =
        (Nat.card (J.TwoRootForest u v) : ℝ) := by
  rw [copiedLaplacian_det_eq_rooted_forest_count J {u, v} ⟨u, Finset.mem_insert_self _ _⟩,
    Finset.coe_insert, Finset.coe_singleton]

end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
