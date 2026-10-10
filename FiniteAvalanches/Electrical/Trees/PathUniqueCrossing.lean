import FiniteAvalanches.Electrical.Trees.ForestEdgeDeletion

/-! A literal copied path crossing a component cut exactly once separates its endpoints. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
open scoped Classical
noncomputable section
variable {V E : Type}

theorem path_interval_reaches (J : CopiedGraph V E) (A : Finset E) (m : ℕ)
    (vertices : Fin (m + 1) → V) (i j : Fin (m + 1)) (hij : i.val ≤ j.val)
    (hsteps : ∀ k : Fin m, i.val ≤ k.val → k.val < j.val →
      J.reaches A (vertices k.castSucc) (vertices k.succ)) :
    J.reaches A (vertices i) (vertices j) := by
  have walk : ∀ n : ℕ, ∀ hn : n ≤ m, i.val ≤ n → n ≤ j.val →
      J.reaches A (vertices i) (vertices ⟨n, Nat.lt_succ_of_le hn⟩) := by
    intro n
    induction n with
    | zero =>
      intro hn hi _
      rw [show i = ⟨0, Nat.lt_succ_of_le hn⟩ from Fin.ext (Nat.le_zero.mp hi)]
      exact .refl
    | succ n ih =>
      intro hn hi hj
      by_cases he : i.val = n + 1
      · rw [show i = ⟨n + 1, Nat.lt_succ_of_le hn⟩ from Fin.ext he]
        exact .refl
      · have hi' : i.val ≤ n := by omega
        have hnm : n < m := by omega
        exact (ih (Nat.le_of_lt hnm) hi' (by omega)).trans
          (hsteps ⟨n, hnm⟩ hi' (by change n < j.val; omega))
  exact walk j.val (Nat.le_of_lt_succ j.isLt) hij (le_refl _)

/-- Exactly one crossing on the entire suffix forces its stated faces to lie apart. -/
theorem path_unique_suffix_crossing_separates (J : CopiedGraph V E) (A : Finset E)
    (m : ℕ) (vertices : Fin (m + 1) → V) (copies : Fin m → E)
    (hends : ∀ k : Fin m,
      (J.left (copies k) = vertices k.castSucc ∧ J.right (copies k) = vertices k.succ) ∨
      (J.right (copies k) = vertices k.castSucc ∧ J.left (copies k) = vertices k.succ))
    (i : Fin (m + 1)) (k : Fin m) (hik : i.val ≤ k.val)
    (hk : ¬J.reaches A (J.left (copies k)) (J.right (copies k)))
    (hu : ∀ l : Fin m, i.val ≤ l.val →
      ¬J.reaches A (J.left (copies l)) (J.right (copies l)) → l = k) :
    ¬J.reaches A (vertices i) (vertices (Fin.last m)) := by
  have steps (l : Fin m) (hil : i.val ≤ l.val) (hlk : l ≠ k) :
      J.reaches A (vertices l.castSucc) (vertices l.succ) := by
    have hl : J.reaches A (J.left (copies l)) (J.right (copies l)) := by
      by_contra hn
      exact hlk (hu l hil hn)
    rcases hends l with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · exact ha ▸ hb ▸ hl
    · exact ha ▸ hb ▸ TwoCopy.reaches_symm J hl
  have hbefore := path_interval_reaches J A m vertices i k.castSucc hik
    (fun l hil hlk => steps l hil (fun h => by
      subst l
      simp only [Fin.val_castSucc] at hlk
      omega))
  have hafter := path_interval_reaches J A m vertices k.succ (Fin.last m)
    (by simp only [Fin.val_succ, Fin.val_last]; omega)
    (fun l hkl _ => steps l (by simp only [Fin.val_succ] at hkl; omega)
      (fun h => by subst l; simp only [Fin.val_succ] at hkl; omega))
  intro h
  have hstep := ((TwoCopy.reaches_symm J hbefore).trans h).trans
    (TwoCopy.reaches_symm J hafter)
  rcases hends k with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · exact hk (ha ▸ hb ▸ hstep)
  · exact hk (ha ▸ hb ▸ TwoCopy.reaches_symm J hstep)

end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
