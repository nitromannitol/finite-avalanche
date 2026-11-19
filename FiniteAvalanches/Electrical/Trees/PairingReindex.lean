import FiniteAvalanches.Electrical.Trees.OrderedPairingMinor
import LatticeProb.Graph.CopiedGraph.RootedMatchingTransport

/-! Reordering terminal lists changes both signed pairing counts and determinants by the same sign. -/

set_option autoImplicit false

namespace FiniteAvalanches.Electrical

open StatementGeometry Polynomial LatticeProb.Combinatorics
open scoped Classical BigOperators

noncomputable section

/-- Independent row and column permutations multiply a determinant coefficient
by the product of their signs. -/
theorem det_coeff_one_submatrix_perm {k : ℕ} (M : Matrix (Fin k) (Fin k) (Polynomial ℝ))
    (α β : Equiv.Perm (Fin k)) :
    ((M.submatrix α β).det).coeff 1 =
      (((Equiv.Perm.sign α : ℤ) : ℝ) * ((Equiv.Perm.sign β : ℤ) : ℝ)) * M.det.coeff 1 := by
  have hm : M.submatrix α β = (M.submatrix α id).submatrix id β := rfl
  rw [hm, Matrix.det_permute', Matrix.det_permute]
  have hα : C (((Equiv.Perm.sign α : ℤ) : ℝ)) =
      (((Equiv.Perm.sign α : ℤ) : Polynomial ℝ)) := by simp
  have hβ : C (((Equiv.Perm.sign β : ℤ) : ℝ)) =
      (((Equiv.Perm.sign β : ℤ) : Polynomial ℝ)) := by simp
  rw [← hα, ← hβ, coeff_C_mul, coeff_C_mul]
  ring

/-- Reordering both terminal lists changes a resistance determinant coefficient
by the product of the two permutation signs. -/
theorem resistanceDet_coeff_one_reindex {V : Type} {k : ℕ} (G : V → V → ℝ)
    (a b : Fin k → V) (α β : Equiv.Perm (Fin k)) :
    ((Matrix.of fun i j : Fin k =>
      (X : Polynomial ℝ) - C ((G (a (α i)) (a (α i)) + G (b (β j)) (b (β j)) -
        2 * G (a (α i)) (b (β j))) / 2)).det).coeff 1 =
      (((Equiv.Perm.sign α : ℤ) : ℝ) * ((Equiv.Perm.sign β : ℤ) : ℝ)) *
        ((Matrix.of fun i j : Fin k =>
          (X : Polynomial ℝ) - C ((G (a i) (a i) + G (b j) (b j) - 2 * G (a i) (b j)) / 2)).det).coeff 1 := by
  exact det_coeff_one_submatrix_perm (Matrix.of fun i j : Fin k =>
    (X : Polynomial ℝ) - C ((G (a i) (a i) + G (b j) (b j) - 2 * G (a i) (b j)) / 2)) α β


/-- The pairing-grove identity for arbitrary injective terminal orders on a
numbered finite vertex carrier. -/
theorem pairingGroves_eq_resistanceDet_fin {d n : ℕ} {E : Type} [Fintype E]
    (J : CopiedGraph (Fin (d + (n + 1))) E)
    (hc : (supportGraph J.left J.right).Preconnected) (g : Fin (d + (n + 1)))
    (a b : Fin (n + 1) → Fin (d + (n + 1)))
    (ha : Function.Injective a) (hb : Function.Injective b) :
    (∑ π : Equiv.Perm (Fin (n + 1)), (((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℝ) *
      (Nat.card (J.PairingGrove a b π) : ℝ)) =
    ((Matrix.of fun i j : Fin (n + 1) =>
      (X : Polynomial ℝ) - C ((groundedGreen J.left J.right g hc (a i) (a i) +
        groundedGreen J.left J.right g hc (b j) (b j) -
        2 * groundedGreen J.left J.right g hc (a i) (b j)) / 2)).det).coeff 1 *
      (Nat.card J.SpanningTree : ℝ) := by
  let I := Finset.univ.image a
  let K := Finset.univ.image b
  have hI : I.card = n + 1 := card_terminal_image a ha
  have hK : K.card = n + 1 := card_terminal_image b hb
  let aa := I.orderEmbOfFin hI
  let bb := K.orderEmbOfFin hK
  let α := terminalOrderPerm a ha
  let β := terminalOrderPerm b hb
  have ha' : a = aa ∘ α := terminal_eq_orderEmbOfFin_comp a ha
  have hb' : b = bb ∘ β := terminal_eq_orderEmbOfFin_comp b hb
  have hcard (x y : Fin (n + 1) → Fin (d + (n + 1))) (hx : Function.Injective x)
      (π : Equiv.Perm (Fin (n + 1))) :
      Nat.card (J.PairingGrove x y π) =
        Nat.card (J.latticeProbGraph.RootedMatchingForest x y π) :=
    Nat.card_congr (J.pairingGroveEquivRootedMatching x y hx π)
  have hcounts := J.latticeProbGraph.signed_rootedMatchingForest_count_eq_ordered
    (R := ℝ) a b ha hb
  change (∑ π : Equiv.Perm (Fin (n + 1)), (((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℝ) *
      (Nat.card (J.latticeProbGraph.RootedMatchingForest a b π) : ℝ)) =
    (((Equiv.Perm.sign α : ℤ) : ℝ) * ((Equiv.Perm.sign β : ℤ) : ℝ)) *
      (∑ π : Equiv.Perm (Fin (n + 1)), (((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℝ) *
        (Nat.card (J.latticeProbGraph.RootedMatchingForest aa bb π) : ℝ)) at hcounts
  simp only [← hcard a b ha, ← hcard aa bb aa.injective] at hcounts
  have hordered := ordered_pairingGroves_eq_resistanceDet J hc g I K hI hK
  have hcoeff := resistanceDet_coeff_one_reindex
    (groundedGreen J.left J.right g hc) aa bb α β
  have ha'' (i : Fin (n + 1)) : aa (α i) = a i := (congrFun ha' i).symm
  have hb'' (i : Fin (n + 1)) : bb (β i) = b i := (congrFun hb' i).symm
  simp only [ha'', hb''] at hcoeff
  change (∑ π : Equiv.Perm (Fin (n + 1)), (((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℝ) *
      (Nat.card (J.PairingGrove a b π) : ℝ)) =
    (((Equiv.Perm.sign α : ℤ) : ℝ) * ((Equiv.Perm.sign β : ℤ) : ℝ)) *
      (∑ π : Equiv.Perm (Fin (n + 1)), (((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℝ) *
        (Nat.card (J.PairingGrove aa bb π) : ℝ)) at hcounts
  dsimp only at hordered
  rw [hcounts, hordered, hcoeff]
  ring

end
end FiniteAvalanches.Electrical
