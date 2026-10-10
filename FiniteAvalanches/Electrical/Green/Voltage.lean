import FiniteAvalanches.Electrical.Green.Grounded
import FiniteAvalanches.Electrical.MaximumPrinciple

/-! Green voltages attain their nonnegative maximum at the injection vertex. -/
namespace FiniteAvalanches.Electrical
open scoped BigOperators Classical
variable {V E : Type*} [Fintype V] [Fintype E]

theorem groundedGreen_diag_nonneg (a b : E → V) (v : V)
    (hc : (supportGraph a b).Preconnected) (u : V) : 0 ≤ groundedGreen a b v hc u u := by
  rw [← energy_groundedGreen_eq]
  exact energy_nonneg a b _

/-- No distinctness or positive-voltage premise is needed, including injection at ground. -/
theorem groundedGreen_range (a b : E → V) (v : V)
    (hc : (supportGraph a b).Preconnected) (u x : V) :
    0 ≤ groundedGreen a b v hc u x ∧ groundedGreen a b v hc u x ≤ groundedGreen a b v hc u u := by
  let B : Finset V := {u,v}
  have hB : ∀ y, ∃ z ∈ B, (supportGraph a b).Reachable y z := fun y => ⟨v,by simp [B],hc y v⟩
  have hM := groundedGreen_diag_nonneg a b v hc u
  have hh : ∀ y, y ∉ B → laplacian a b (groundedGreen a b v hc u) y = 0 := by
    intro y hy
    have hu : y ≠ u := fun h => hy (by simp [B,h])
    have hv : y ≠ v := fun h => hy (by simp [B,h])
    rw [groundedGreen_laplacian a b v hc u y hv,if_neg hu]
  have hup := le_of_harmonic a b B hB (groundedGreen a b v hc u) (groundedGreen a b v hc u u)
    (by
      intro y hy
      have h : y = u ∨ y = v := by simpa [B] using hy
      rcases h with rfl | rfl
      · exact le_rfl
      · rw [groundedGreen_ground]; exact hM) hh x
  have hlo := le_of_harmonic a b B hB ((-1 : ℝ) • groundedGreen a b v hc u) 0
    (by
      intro y hy
      have h : y = u ∨ y = v := by simpa [B] using hy
      rcases h with h | h
      · rw [h]
        change -1*groundedGreen a b v hc u u ≤ 0
        linarith only [hM]
      · rw [h]
        simp only [Pi.smul_apply,smul_eq_mul,groundedGreen_ground,mul_zero,le_refl])
    (by intro y hy; rw [laplacian_smul,hh y hy,mul_zero]) x
  change -1*groundedGreen a b v hc u x ≤ 0 at hlo
  exact ⟨by linarith only [hlo],hup⟩

/-- The source W_i is nonnegative on the actual whole vertex carrier. -/
theorem groundedGreen_diag_sub_source_nonneg (a b : E → V) (v : V)
    (hc : (supportGraph a b).Preconnected) (u x : V) :
    0 ≤ groundedGreen a b v hc x x-groundedGreen a b v hc u x := by
  have h := (groundedGreen_range a b v hc x u).2
  rw [groundedGreen_symm a b v hc x u] at h
  linarith only [h]

end FiniteAvalanches.Electrical
