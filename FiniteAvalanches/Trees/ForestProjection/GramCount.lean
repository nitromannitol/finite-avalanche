import FiniteAvalanches.Trees.ForestProjection.Incidence
import FiniteAvalanches.External.AllMinorsMatrixTree

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix
namespace FiniteAvalanches.ForestGramCounting
open FiniteAvalanches.Trees FiniteAvalanches.Trees.Multigraph
open FiniteAvalanches.External

variable {n : ℕ} {E : Type} [Fintype E] (G : Multigraph (Fin n) E)

/-- The positive copied Laplacian with the literal all-minors body. -/
def fullCopiedLaplacian : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun x y => ∑ e : E,
    ((if x = G.left e then (1 : ℝ) else 0) - (if x = G.right e then 1 else 0)) *
      ((if y = G.left e then (1 : ℝ) else 0) - (if y = G.right e then 1 else 0)))

theorem fullCopiedLaplacian_restrict (R : Finset (Fin n)) (x y : {v : Fin n // v ∉ R}) :
    fullCopiedLaplacian G x.val y.val = G.rootGram R x y := by
  simp only [fullCopiedLaplacian, Matrix.of_apply, rootGram, Matrix.mul_apply,
    Matrix.transpose_apply, G.rootIncidence_apply, eq_comm]

/-- Root uniqueness kills every nonidentity root matching in a principal all-minors sum. -/
theorem root_matching_eq_one (R : Finset (Fin n)) (π : Equiv.Perm (Fin R.card))
    (F : G.RootedForest (R : Set (Fin n)))
    (h : ∀ r, G.reaches F.val (R.orderEmbOfFin rfl r) (R.orderEmbOfFin rfl (π r))) :
    π = 1 := by
  apply Equiv.ext
  intro r
  change π r = r
  obtain ⟨root, _, _, hu⟩ := F.property.2 (R.orderEmbOfFin rfl r)
  have hx := hu _ (Finset.orderEmbOfFin_mem R rfl r) Relation.ReflTransGen.refl
  have hy := hu _ (Finset.orderEmbOfFin_mem R rfl (π r)) (h r)
  exact (R.orderEmbOfFin rfl).injective (hy.trans hx.symm)

/-- Literal principal all-minors consumption, with no connectivity assumption on the graph. -/
theorem det_principal_eq_original_forest_count (R : Finset (Fin n)) (hR : R.Nonempty) :
    ((fullCopiedLaplacian G).submatrix
      (Rᶜ.orderEmbOfFin (by rw [Finset.card_compl, Fintype.card_fin]))
      (Rᶜ.orderEmbOfFin (by rw [Finset.card_compl, Fintype.card_fin]))).det =
      (Nat.card (G.RootedForest (R : Set (Fin n))) : ℝ) := by
  have h := allMinors_matrixTree G R R rfl rfl (Finset.one_le_card.mpr hR)
  change ((fullCopiedLaplacian G).submatrix _ _).det = _ at h
  have hsign : (-1 : ℝ) ^ ((∑ x ∈ R, (x : ℕ)) + (∑ y ∈ R, (y : ℕ))) = 1 := by
    rw [← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [hsign, one_mul, Finset.sum_eq_single (1 : Equiv.Perm (Fin R.card))] at h
  · rw [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul] at h
    refine h.trans ?_
    congr 1
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro F
    constructor
    · exact And.left
    · intro hF
      exact ⟨hF, fun r => by rw [Equiv.Perm.one_apply]; exact .refl⟩
  · intro π _ hπ
    haveI : IsEmpty {F : Finset E // G.is_rooted_forest (R : Set (Fin n)) F ∧
        ∀ r : Fin R.card, G.reaches F (R.orderEmbOfFin rfl r) (R.orderEmbOfFin rfl (π r))} :=
      ⟨fun F => hπ (root_matching_eq_one G R π ⟨F.val, F.property.1⟩ F.property.2)⟩
    rw [Nat.card_of_isEmpty, Nat.cast_zero, mul_zero]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

/-- Enumeration of the actual nonroot columns used by the all-minors export. -/
def nonrootEnumeration (R : Finset (Fin n)) : Fin (n - R.card) ≃ {v : Fin n // v ∉ R} :=
  (Rᶜ.orderIsoOfFin (by rw [Finset.card_compl, Fintype.card_fin])).toEquiv.trans
    { toFun := fun v => ⟨v.val, Finset.mem_compl.mp v.property⟩
      invFun := fun v => ⟨v.val, Finset.mem_compl.mpr v.property⟩
      left_inv := fun v => rfl
      right_inv := fun v => rfl }

/-- The normalizer is the original copied-forest count, including disconnected deletions. -/
theorem gram_det_eq_original_forest_count (R : Finset (Fin n)) (hR : R.Nonempty) :
    (G.rootGram R).det = (Nat.card (G.RootedForest (R : Set (Fin n))) : ℝ) := by
  rw [← Matrix.det_submatrix_equiv_self (nonrootEnumeration R) (G.rootGram R)]
  convert det_principal_eq_original_forest_count G R hR using 2
  ext x y
  exact (fullCopiedLaplacian_restrict G R (nonrootEnumeration R x) (nonrootEnumeration R y)).symm

end FiniteAvalanches.ForestGramCounting
