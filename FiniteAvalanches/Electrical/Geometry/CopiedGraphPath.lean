import FiniteAvalanches.Electrical.Geometry.CopiedGraphConnectivity

/-! Walking along an ordered list of original copied edges. -/
namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
open scoped Classical
variable {V E : Type} (J : CopiedGraph V E)

/-- Traverse the original copies in their actual finite consecutive-vertex order. -/
theorem reaches_of_ordered_copies {F : Finset E} (m : ℕ)
    (vertices : Fin (m + 1) → V) (copies : Fin m → E)
    (hcopies : ∀ i : Fin m, copies i ∈ F)
    (hends : ∀ i : Fin m,
      (J.left (copies i) = vertices i.castSucc ∧
        J.right (copies i) = vertices i.succ) ∨
      (J.right (copies i) = vertices i.castSucc ∧
        J.left (copies i) = vertices i.succ)) :
    J.reaches F (vertices 0) (vertices (Fin.last m)) := by
  have hwalk : ∀ (k : ℕ) (hk : k ≤ m),
      J.reaches F (vertices 0) (vertices ⟨k, Nat.lt_succ_of_le hk⟩) := by
    intro k
    induction k with
    | zero =>
      intro hk
      exact .refl
    | succ k ih =>
      intro hk
      have hkm : k < m := Nat.lt_of_succ_le hk
      let i : Fin m := ⟨k, hkm⟩
      have hprev := ih (Nat.le_of_lt hkm)
      have hstep : J.reaches F (vertices i.castSucc) (vertices i.succ) :=
        .single ⟨copies i, hcopies i, hends i⟩
      exact hprev.trans hstep
  exact hwalk m (Nat.le_refl m)

end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
