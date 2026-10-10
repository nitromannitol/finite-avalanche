import FiniteAvalanches.Electrical.ForestColor.Enumeration

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.ForestColor
open Trees ForestGramCounting External
open scoped Classical BigOperators Matrix
noncomputable section
variable {n : ℕ} {E : Type} [Fintype E] (G : Multigraph (Fin (n + 2)) E)

def groundedMatrix : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (fullCopiedLaplacian G).submatrix Fin.succ Fin.succ

theorem matching_identity (j : Fin (n + 1)) (π : Equiv.Perm (Fin 2))
    (F : G.RootedForest (rootPair (0 : Fin (n + 1)) : Set (Fin (n + 2))))
    (h : ∀ r : Fin 2, G.reaches F.val
      ((rootPair (0 : Fin (n + 1))).orderEmbOfFin (rootPair_card _) r)
      ((rootPair j).orderEmbOfFin (rootPair_card _) (π r))) : π = 1 := by
  have hπ1 : π 1 ≠ 0 := by
    intro hp
    have hh := h 1
    rw [rootPair_enumeration, rootPair_enumeration, hp] at hh
    simp only [show (1 : Fin 2) ≠ 0 by decide, if_false, if_true,
      show (0 : Fin (n + 1)).succ = (1 : Fin (n + 2)) by rfl] at hh
    obtain ⟨r, _, _, hu⟩ := F.property.2 (1 : Fin (n + 2))
    have hb := hu 1 (by simp [rootPair]) .refl
    have ha := hu 0 (by simp [rootPair]) hh
    have he : (0 : Fin (n + 2)) = 1 := ha.trans hb.symm
    have he' := congrArg Fin.val he
    norm_num at he'
  have hπ1eq : π 1 = 1 := by
    apply Fin.ext
    have hlt := (π 1).isLt
    have hne : (π 1).val ≠ 0 := fun h => hπ1 (Fin.ext h)
    change (π 1).val = 1
    omega
  have hπ0eq : π 0 = 0 := by
    have hne : π 0 ≠ 1 := by
      intro hzero
      have he := π.injective (hzero.trans hπ1eq.symm)
      norm_num at he
    apply Fin.ext
    have hlt := (π 0).isLt
    have hv : (π 0).val ≠ 1 := fun h => hne (Fin.ext h)
    change (π 0).val = 0
    omega
  apply Equiv.ext
  intro r
  fin_cases r
  · exact hπ0eq
  · exact hπ1eq

/-- A signed nonprincipal minor counts the actual one-root color event, on original copies. -/
theorem adjugate_eq_color_count (j : Fin (n + 1)) :
    (groundedMatrix G).adjugate j 0 =
      (Nat.card {F : G.RootedForest
        (rootPair (0 : Fin (n + 1)) : Set (Fin (n + 2))) //
          G.reaches F.val j.succ (1 : Fin (n + 2))} : ℝ) := by
  have h := allMinors_matrixTree G (rootPair (0 : Fin (n + 1))) (rootPair j)
    (rootPair_card _) (rootPair_card _) (by omega : 1 ≤ 2)
  change ((fullCopiedLaplacian G).submatrix _ _).det = _ at h
  have hsign : (-1 : ℝ) ^ ((∑ x ∈ rootPair (0 : Fin (n + 1)), (x : ℕ)) +
      (∑ x ∈ rootPair j, (x : ℕ))) = (-1 : ℝ) ^ (j : ℕ) := by
    simp [rootPair, Ne.symm (Fin.succ_ne_zero j), pow_add, Nat.add_left_comm]
  rw [hsign, Finset.sum_eq_single (1 : Equiv.Perm (Fin 2))] at h
  · rw [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul] at h
    have hm : ((fullCopiedLaplacian G).submatrix
        ((rootPair (0 : Fin (n + 1)))ᶜ.orderEmbOfFin (rootPair_compl_card _))
        ((rootPair j)ᶜ.orderEmbOfFin (rootPair_compl_card _))) =
        (groundedMatrix G).submatrix (0 : Fin (n + 1)).succAbove j.succAbove := by
      ext x y
      rw [Matrix.submatrix_apply, rootPair_compl_enumeration, rootPair_compl_enumeration]
      simp [groundedMatrix, Matrix.submatrix_apply, Fin.succAbove_zero]
    change ((fullCopiedLaplacian G).submatrix
      ((rootPair (0 : Fin (n + 1)))ᶜ.orderEmbOfFin (rootPair_compl_card _))
      ((rootPair j)ᶜ.orderEmbOfFin (rootPair_compl_card _))).det = _ at h
    rw [hm] at h
    have hc : Nat.card {F : Finset E //
        G.is_rooted_forest (rootPair (0 : Fin (n + 1)) : Set (Fin (n + 2))) F ∧
        ∀ r : Fin 2, G.reaches F
          ((rootPair (0 : Fin (n + 1))).orderEmbOfFin (rootPair_card _) r)
          ((rootPair j).orderEmbOfFin (rootPair_card _) ((1 : Equiv.Perm (Fin 2)) r))} =
        Nat.card {F : G.RootedForest
          (rootPair (0 : Fin (n + 1)) : Set (Fin (n + 2))) //
          G.reaches F.val j.succ (1 : Fin (n + 2))} := by
      apply Nat.card_congr
      refine { toFun := fun F => ⟨⟨F.val, F.property.1⟩, ?_⟩
               invFun := fun F => ⟨F.val.val, F.val.property, ?_⟩
               left_inv := fun _ => rfl
               right_inv := fun _ => rfl }
      · have h1 := F.property.2 1
        simp only [Equiv.Perm.one_apply, rootPair_enumeration,
          show (1 : Fin 2) ≠ 0 by decide, if_false] at h1
        exact G.reaches_symm h1
      · intro r
        fin_cases r
        · simp only [Equiv.Perm.one_apply, rootPair_enumeration]
          exact .refl
        · simp only [Equiv.Perm.one_apply, rootPair_enumeration]
          exact G.reaches_symm F.property
    rw [hc] at h
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    simp only [Fin.val_zero, zero_add]
    rw [h]
    rw [← mul_assoc, ← pow_add]
    have he : (j : ℕ) + (j : ℕ) = 2 * (j : ℕ) := by omega
    rw [he, pow_mul, neg_one_sq, one_pow, one_mul]
  · intro π _ hπ
    haveI : IsEmpty {F : Finset E //
        G.is_rooted_forest (rootPair (0 : Fin (n + 1)) : Set (Fin (n + 2))) F ∧
        ∀ r : Fin 2, G.reaches F
          ((rootPair (0 : Fin (n + 1))).orderEmbOfFin (rootPair_card _) r)
          ((rootPair j).orderEmbOfFin (rootPair_card _) (π r))} :=
      ⟨fun F => hπ (matching_identity G j π ⟨F.val, F.property.1⟩ F.property.2)⟩
    rw [Nat.card_of_isEmpty, Nat.cast_zero, mul_zero]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

end
end FiniteAvalanches.Electrical.ForestColor
