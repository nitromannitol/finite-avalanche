import LatticeProb.Graph.CopiedGraph.AllMinorsMatrixTree
import FiniteAvalanches.Trees.RootedForests
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Finset.Sort

/-!
External theorem: the all-minors matrix-tree theorem for a finite loopless edge-copy multigraph.

Source: S. Chaiken, "A combinatorial proof of the all minors matrix tree theorem", SIAM J.
Algebraic Discrete Methods 3 (1982), equation (2); complete proof in A. Zernik, "Taylor expansion
proof of the matrix tree theorem, part II", arXiv:1308.2160v1, Theorem 2 with Definition 4.

The matrix is the positive Laplacian `L x y = ∑ e, (δ x (left e) - δ x (right e)) *
(δ y (left e) - δ y (right e))`, with every original copy counted once. Rows `I` and columns `J`
are deleted and the remaining indices are enumerated increasingly. Forests are rooted at `I`; the
permutation `π` pairs the `r`-th element of `I` with the `π r`-th element of `J` in the same tree.
-/
set_option autoImplicit false

namespace FiniteAvalanches.External

open FiniteAvalanches.Trees
open scoped BigOperators Classical

theorem allMinors_matrixTree {n k : ℕ} {E : Type} [Fintype E]
    (G : Multigraph (Fin n) E) (I J : Finset (Fin n)) (hI : I.card = k) (hJ : J.card = k) (hk : 1 ≤ k) :
    ((Matrix.of (fun x y : Fin n => ∑ e : E,
          ((if x = G.left e then (1 : ℝ) else 0) - (if x = G.right e then (1 : ℝ) else 0)) *
            ((if y = G.left e then (1 : ℝ) else 0) - (if y = G.right e then (1 : ℝ) else 0))) :
        Matrix (Fin n) (Fin n) ℝ).submatrix
      (Iᶜ.orderEmbOfFin (show Iᶜ.card = n - k by rw [Finset.card_compl, Fintype.card_fin, hI]))
      (Jᶜ.orderEmbOfFin (show Jᶜ.card = n - k by rw [Finset.card_compl, Fintype.card_fin, hJ]))).det =
      (-1 : ℝ) ^ ((∑ x ∈ I, (x : ℕ)) + (∑ y ∈ J, (y : ℕ))) *
        ∑ π : Equiv.Perm (Fin k), ((Equiv.Perm.sign π : ℤ) : ℝ) *
          (Nat.card {F : Finset E // G.is_rooted_forest (I : Set (Fin n)) F ∧
            ∀ r : Fin k, G.reaches F (I.orderEmbOfFin hI r) (J.orderEmbOfFin hJ (π r))} : ℝ) := by
  have hcard : I.card ≤ n := by simpa using I.card_le_univ
  have hkn : k ≤ n := by
    have := hk
    omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hkn
  have hn : n = d + k := by omega
  clear hd
  subst n
  let H : LatticeProb.Graph.CopiedGraph (Fin (d + k)) E := ⟨G.left, G.right⟩
  have h := H.det_laplacian_minor (R := ℝ) I J hI hJ
  let minor (m : ℕ) (hI' : Iᶜ.card = m) (hJ' : Jᶜ.card = m) : ℝ :=
    ((Matrix.of (fun x y : Fin (d + k) => ∑ e : E,
      ((if x = G.left e then (1 : ℝ) else 0) - (if x = G.right e then 1 else 0)) *
      ((if y = G.left e then (1 : ℝ) else 0) - (if y = G.right e then 1 else 0))) :
        Matrix (Fin (d + k)) (Fin (d + k)) ℝ).submatrix
          (Iᶜ.orderEmbOfFin hI') (Jᶜ.orderEmbOfFin hJ')).det
  change minor ((d + k) - k) _ _ = _
  change minor d _ _ = _ at h
  convert h using 1
  · simp only [Nat.add_sub_cancel]
  · rfl

end FiniteAvalanches.External
