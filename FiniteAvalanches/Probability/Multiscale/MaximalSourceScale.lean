import FiniteAvalanches.Probability.Multiscale.ScaleExponent

/-! The maximal actual source scale, with no loss from doubled indices. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Probability.CurrentScale
open scoped Classical

/-- Scale growth gives a finite search bound for the maximal source index. -/
theorem index_le_scale (b : ℕ) (hb : 6 ≤ b) (i : ℕ) : i ≤ scale b i := by
  have hi : i ≤ b ^ i := (Nat.lt_pow_self (by omega : 1 < b)).le
  exact hi.trans (Nat.lt_two_pow_self.le)

/-- For every large integer diameter, there is a last source scale satisfying
the paper's factor-sixteen condition, and its next consecutive scale fails it. -/
theorem exists_maximal_source_scale (b : ℕ) (hb : 6 ≤ b) (d : ℕ)
    (hd : 16 * scale b 2 ≤ d) :
    ∃ n : ℕ, 2 ≤ n ∧ 16 * scale b n ≤ d ∧ d < 16 * scale b (n + 1) := by
  let P : ℕ → Prop := fun i => 16 * scale b i ≤ d
  let n := Nat.findGreatest P d
  have h2 : 2 ≤ d := by
    have hs := index_le_scale b hb 2
    omega
  have hn : 2 ≤ n := Nat.le_findGreatest h2 hd
  have hPn : P n := Nat.findGreatest_spec h2 hd
  have hmax := (Nat.findGreatest_eq_iff.mp (rfl : Nat.findGreatest P d = n)).2.2
  have hnext : ¬ P (n + 1) := by
    by_cases hnd : n + 1 ≤ d
    · exact hmax (by omega) hnd
    · have hs := index_le_scale b hb (n + 1)
      dsimp only [P]
      omega
  exact ⟨n, hn, hPn, Nat.lt_of_not_ge hnext⟩

end FiniteAvalanches.Probability.CurrentScale
