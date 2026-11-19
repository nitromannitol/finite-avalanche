import FiniteAvalanches.Electrical.Trees.ResistanceComplement
import FiniteAvalanches.Electrical.Trees.PairingForestBridge
import LatticeProb.Graph.CopiedGraph.AllMinorsMatrixTree
import LatticeProb.LinearAlgebra.OrderedComplementSign

/-! The all-minors identity for increasing terminal lists and resistance coefficients. -/

set_option autoImplicit false

namespace FiniteAvalanches.Electrical

open StatementGeometry ChordSplit Polynomial LatticeProb.LinearAlgebra
open scoped Classical BigOperators

noncomputable section

/-- For increasing terminal lists, the signed pairing-grove count is the
resistance coefficient times the number of spanning trees. -/
theorem ordered_pairingGroves_eq_resistanceDet {d n : ℕ} {E : Type} [Fintype E]
    (J : CopiedGraph (Fin (d + (n + 1))) E)
    (hc : (supportGraph J.left J.right).Preconnected) (g : Fin (d + (n + 1)))
    (I K : Finset (Fin (d + (n + 1)))) (hI : I.card = n + 1) (hK : K.card = n + 1) :
    let a := I.orderEmbOfFin hI
    let b := K.orderEmbOfFin hK
    (∑ π : Equiv.Perm (Fin (n + 1)), (((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℝ) *
      (Nat.card (J.PairingGrove a b π) : ℝ)) =
    ((Matrix.of fun i j : Fin (n + 1) =>
      (X : Polynomial ℝ) - C ((groundedGreen J.left J.right g hc (a i) (a i) +
        groundedGreen J.left J.right g hc (b j) (b j) -
        2 * groundedGreen J.left J.right g hc (a i) (b j)) / 2)).det).coeff 1 *
      (Nat.card J.SpanningTree : ℝ) := by
  dsimp only
  have hCI : Iᶜ.card = d := by
    rw [Finset.card_compl, Fintype.card_fin, hI, Nat.add_sub_cancel]
  have hCK : Kᶜ.card = d := by
    rw [Finset.card_compl, Fintype.card_fin, hK, Nat.add_sub_cancel]
  let e := increasingComplementRootEquiv I hI hCI
  let f := increasingComplementRootEquiv K hK hCK
  let L := J.latticeProbGraph
  let s : ℝ := (-1) ^ ((∑ x ∈ I, (x : ℕ)) + (∑ y ∈ K, (y : ℕ)))
  have hsign : ((Equiv.Perm.sign (f.trans e.symm) : ℤ) : ℝ) = s := by
    dsimp only [s, e, f]
    exact_mod_cast sign_increasingComplementRootEquiv_trans_symm I K hI hK hCI hCK
  have hs : s * s = 1 := by
    dsimp [s]
    rw [← mul_pow]
    norm_num
  have hcount (π : Equiv.Perm (Fin (n + 1))) :
      Nat.card (J.PairingGrove (I.orderEmbOfFin hI) (K.orderEmbOfFin hK) π) =
        Nat.card {F : Finset E // L.IsRootedForest (I : Set _) F ∧
          ∀ r, L.reaches F (I.orderEmbOfFin hI r) (K.orderEmbOfFin hK (π r))} := by
    have he := Nat.card_congr (J.pairingGroveEquivRootedMatching
      (I.orderEmbOfFin hI) (K.orderEmbOfFin hK) (I.orderEmbOfFin hI).injective π)
    simpa only [Finset.range_orderEmbOfFin, L] using he
  have htree := L.det_laplacian_minor (R := ℝ) I K hI hK
  have hLap : (Matrix.of fun x y : Fin (d + (n + 1)) => ∑ z : E,
      ((if x = L.left z then (1 : ℝ) else 0) - (if x = L.right z then 1 else 0)) *
        ((if y = L.left z then 1 else 0) - (if y = L.right z then 1 else 0))) =
      copiedLaplacian J := by
    ext x y
    simp only [Matrix.of_apply, copiedLaplacian, L, CopiedGraph.latticeProbGraph, eq_comm]
  rw [hLap] at htree
  have hminor : ((copiedLaplacian J).submatrix
      (Iᶜ.orderEmbOfFin hCI) (Kᶜ.orderEmbOfFin hCK)).det =
      s * ∑ π : Equiv.Perm (Fin (n + 1)), (((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℝ) *
        (Nat.card (J.PairingGrove (I.orderEmbOfFin hI) (K.orderEmbOfFin hK) π) : ℝ) := by
    simpa only [s, ← hcount] using htree
  have hres := resistanceDet_coeff_mul_tree_count J hc g e f
  change ((Matrix.of fun i j : Fin (n + 1) =>
      (X : Polynomial ℝ) - C ((groundedGreen J.left J.right g hc
        (I.orderEmbOfFin hI i) (I.orderEmbOfFin hI i) +
        groundedGreen J.left J.right g hc (K.orderEmbOfFin hK j) (K.orderEmbOfFin hK j) -
        2 * groundedGreen J.left J.right g hc (I.orderEmbOfFin hI i)
          (K.orderEmbOfFin hK j)) / 2)).det).coeff 1 *
      (Nat.card J.SpanningTree : ℝ) =
    ((Equiv.Perm.sign (f.trans e.symm) : ℤ) : ℝ) *
      ((copiedLaplacian J).submatrix (Iᶜ.orderEmbOfFin hCI)
        (Kᶜ.orderEmbOfFin hCK)).det at hres
  rw [hsign, hminor, ← mul_assoc, hs, one_mul] at hres
  exact hres.symm

end
end FiniteAvalanches.Electrical
