import FiniteAvalanches.Sandpile.Recurrence.RawGraphLaplacian
import Mathlib.Algebra.Order.Floor.Semiring

/-! A positive natural firing script is constructed from an ordinary Poisson
solution; bounded rounding errors are paid for by a fixed finite scaling. -/
namespace FiniteAvalanches.Sandpile.RawGraph
open FiniteAvalanches.Sandpile
open scoped Classical BigOperators
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : FiniteAvalanches.Trees.Multigraph V E) (s : V)

theorem poisson_nonnegative (f : V → ℝ) (hs : f s = 0)
    (hf : ∀ x, x ≠ s → lapReal G f x = 1) : ∀ x, 0 ≤ f x := by
  obtain ⟨z, _, hz⟩ := Finset.exists_min_image (Finset.univ : Finset V) f
    ⟨s, Finset.mem_univ _⟩
  have hm : ∀ y, f z ≤ f y := fun y => hz y (Finset.mem_univ _)
  have he : z = s := by
    by_contra hn
    have hl : lapReal G f z ≤ 0 := by
      unfold lapReal
      apply Finset.sum_nonpos
      intro y _
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (sub_nonpos.mpr (hm y))
    rw [hf z hn] at hl
    norm_num at hl
  intro x
  simpa only [he, hs] using hm x

/-- Connectedness is actual walk connectedness of the copied graph's support. -/
theorem exists_positive_script
    (hc : (FiniteAvalanches.Electrical.supportGraph G.left G.right).Preconnected) :
    ∃ n : V → ℕ, n s = 0 ∧ ∀ x, x ≠ s → 1 ≤ lapInt G (fun y => n y) x := by
  obtain ⟨f, hf, _⟩ := FiniteAvalanches.Electrical.existsUnique_grounded_poisson
    G.left G.right s hc (fun _ => 1)
  have hl : ∀ x, x ≠ s → lapReal G f x = 1 := by
    intro x hx
    rw [lap_real_eq_electrical, hf.2 x hx]
  have hn := poisson_nonnegative G s f hf.1 hl
  let M : ℕ := (∑ v, Burning.degree G v) + 1
  let n : V → ℕ := fun x => ⌊(M : ℝ) * f x⌋₊
  refine ⟨n, ?_, ?_⟩
  · simp [n, hf.1]
  · intro x hx
    have hr : (1 : ℝ) ≤ lapReal G (fun y => (n y : ℝ)) x := by
      have hround : ∀ y, (M : ℝ) * (f x - f y) - 1 ≤ (n x : ℝ) - n y := by
        intro y
        have hxlo := Nat.sub_one_lt_floor ((M : ℝ) * f x)
        have hyup := Nat.floor_le (mul_nonneg (Nat.cast_nonneg M) (hn y))
        change _ < (n x : ℝ) at hxlo
        change (n y : ℝ) ≤ _ at hyup
        linarith
      have hsum : (M : ℝ) * lapReal G f x - (Burning.degree G x : ℝ) ≤
          lapReal G (fun y => (n y : ℝ)) x := by
        calc
          _ = ∑ y, (copies G x y : ℝ) * ((M : ℝ) * (f x - f y) - 1) := by
            rw [degree_eq_sum_copies, Nat.cast_sum]
            simp only [lapReal, Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun _ _ => by ring
          _ ≤ _ := Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (hround y) (Nat.cast_nonneg _)
      have hdeg : Burning.degree G x ≤ ∑ v, Burning.degree G v :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
      have hd : (Burning.degree G x : ℝ) ≤ ∑ v, (Burning.degree G v : ℝ) := by
        exact_mod_cast hdeg
      rw [hl x hx] at hsum
      have hm : (M : ℝ) = (∑ v, (Burning.degree G v : ℝ)) + 1 := by
        simp only [M, Nat.cast_add, Nat.cast_one, Nat.cast_sum]
      rw [hm] at hsum
      linarith
    have he : lapReal G (fun y => (n y : ℝ)) x =
        (lapInt G (fun y => (n y : ℤ)) x : ℝ) := by
      simpa only [Int.cast_natCast] using lap_real_eq_cast G (fun y => (n y : ℤ)) x
    rw [he] at hr
    exact_mod_cast hr

end
end FiniteAvalanches.Sandpile.RawGraph
