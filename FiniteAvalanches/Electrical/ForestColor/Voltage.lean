import FiniteAvalanches.Electrical.ForestColor.Cofactor
import FiniteAvalanches.Electrical.ForestColor.Laplacian
import FiniteAvalanches.Trees.ForestProjection.Uniform
import FiniteAvalanches.Electrical.SplitResponse

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.ForestColor
open Trees ForestGramCounting
open scoped Classical BigOperators Matrix
noncomputable section
variable {n : ℕ} {E : Type} [Fintype E] (G : Multigraph (Fin (n + 2)) E)

abbrev Forest := G.RootedForest (rootPair (0 : Fin (n + 1)) : Set (Fin (n + 2)))

/-- The literal fraction of all original copied two-root forests with beta color. -/
def colorMass (x : Fin (n + 2)) : ℝ :=
  (Nat.card {F : Forest G // G.reaches F.val x (1 : Fin (n + 2))} : ℝ) /
    (Nat.card (Forest G) : ℝ)

theorem colorMass_zero : colorMass G 0 = 0 := by
  haveI : IsEmpty {F : Forest G // G.reaches F.val 0 (1 : Fin (n + 2))} := ⟨by
    intro F
    obtain ⟨r, _, _, hu⟩ := F.val.property.2 0
    have ha := hu 0 (by simp [rootPair]) .refl
    have hb := hu 1 (by simp [rootPair]) F.property
    have h := congrArg Fin.val (ha.trans hb.symm)
    norm_num at h⟩
  simp [colorMass]

theorem forest_count_pos (hconn : ∀ x y, G.reaches Finset.univ x y) :
    0 < (Nat.card (Forest G) : ℝ) := by
  haveI : Nonempty (Forest G) := G.nonempty_rootedForest _
    (by exact ⟨0, by simp [rootPair]⟩) hconn
  exact_mod_cast (Nat.card_pos (α := Forest G))

theorem colorMass_one (hconn : ∀ x y, G.reaches Finset.univ x y) : colorMass G 1 = 1 := by
  have he : {F : Forest G // G.reaches F.val (1 : Fin (n + 2)) 1} ≃ Forest G :=
    { toFun := Subtype.val
      invFun := fun F => ⟨F, .refl⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold colorMass
  rw [Nat.card_congr he]
  exact div_self (ne_of_gt (forest_count_pos G hconn))

theorem colorMass_succ (j : Fin (n + 1)) :
    colorMass G j.succ = (groundedMatrix G).adjugate j 0 / (Nat.card (Forest G) : ℝ) := by
  rw [adjugate_eq_color_count]
  rfl

theorem groundedMatrix_mulVec (u : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    (groundedMatrix G *ᵥ u) j = laplacian G.left G.right (Fin.cases 0 u) j.succ := by
  rw [← fullCopiedLaplacian_mulVec]
  simp [groundedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The actual color fraction is harmonic at every vertex other than the two roots. -/
theorem colorMass_harmonic (x : Fin (n + 2)) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    laplacian G.left G.right (colorMass G) x = 0 := by
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hx0
  have hj : j ≠ 0 := by intro h; subst j; exact hx1 rfl
  have hpot : colorMass G = Fin.cases 0 (fun j => colorMass G j.succ) := by
    funext y
    refine Fin.cases ?_ (fun k => ?_) y
    · exact colorMass_zero G
    · rfl
  rw [hpot, ← groundedMatrix_mulVec]
  simp_rw [colorMass_succ]
  simp only [Matrix.mulVec, dotProduct, ← mul_div_assoc, ← Finset.sum_div]
  have h := congrArg (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => A j 0)
    (Matrix.mul_adjugate (groundedMatrix G))
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    if_neg hj, mul_zero] at h
  rw [h, zero_div]

/-- Color probabilities equal every fully characterized zero/one voltage; no marginal is assumed. -/
theorem colorMass_eq_voltage (hconn : ∀ x y, G.reaches Finset.univ x y)
    (phi : Fin (n + 2) → ℝ) (h0 : phi 0 = 0) (h1 : phi 1 = 1)
    (hh : ∀ x, x ≠ 0 → x ≠ 1 → laplacian G.left G.right phi x = 0) :
    colorMass G = phi := by
  apply eq_of_harmonic_boundary G.left G.right {0, 1}
    (fun x => ⟨0, by simp, (G.supportGraph_preconnected_of_reaches hconn) x 0⟩)
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · rw [colorMass_zero, h0]
    · rw [colorMass_one G hconn, h1]
  · intro x hx
    exact colorMass_harmonic G x (by simpa using hx : x ≠ 0 ∧ x ≠ 1).1
      (by simpa using hx : x ≠ 0 ∧ x ≠ 1).2
  · intro x hx
    exact hh x (by simpa using hx : x ≠ 0 ∧ x ≠ 1).1
      (by simpa using hx : x ≠ 0 ∧ x ≠ 1).2

end
end FiniteAvalanches.Electrical.ForestColor
