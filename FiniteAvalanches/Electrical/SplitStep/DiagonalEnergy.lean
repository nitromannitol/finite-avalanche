import FiniteAvalanches.Electrical.ChordSplit.IdentifiedResponse
import FiniteAvalanches.Electrical.Plane.TrialResponse

set_option autoImplicit false

namespace FiniteAvalanches.Electrical.SplitStep
open scoped Classical BigOperators

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The unsymmetrized ground transform retains the inward current at the one terminal. -/
theorem ground_energy_eq_current (a b : E → V) (r : Fin 3 → V)
    (hr : Function.Injective r) (phi f : V → ℝ)
    (hp0 : phi (r 0) = 0) (hp1 : phi (r 1) = 0) (hp2 : phi (r 2) = 1)
    (hf0 : f (r 0) = 0) (hf1 : f (r 1) = 1)
    (hp : ∀ x, x ∉ terminalSet r → laplacian a b phi x = 0) :
    energy a b (fun x => (1 - phi x) * f x) =
      weightedEnergy a b (fun x => 1 - phi x) f - laplacian a b phi (r 1) := by
  rw [ground_identity]
  have ht (i : Fin 3) :
      (1 - phi (r i)) * f (r i) ^ 2 *
        laplacian a b (fun x => 1 - phi x) (r i) =
          if i = 1 then -laplacian a b phi (r 1) else 0 := by
    rw [laplacian_one_sub]
    fin_cases i
    · change (1 - phi (r 0)) * f (r 0) ^ 2 * -laplacian a b phi (r 0) =
        if (0 : Fin 3) = 1 then -laplacian a b phi (r 1) else 0
      rw [hp0, hf0, if_neg (by decide)]
      ring
    · change (1 - phi (r 1)) * f (r 1) ^ 2 * -laplacian a b phi (r 1) =
        if (1 : Fin 3) = 1 then -laplacian a b phi (r 1) else 0
      rw [hp1, hf1, if_pos rfl]
      ring
    · change (1 - phi (r 2)) * f (r 2) ^ 2 * -laplacian a b phi (r 2) =
        if (2 : Fin 3) = 1 then -laplacian a b phi (r 1) else 0
      rw [hp2, if_neg (by decide)]
      ring
  rw [sum_eq_terminal_sum r hr _ (by
    intro x hx
    rw [laplacian_one_sub, hp x hx, neg_zero, mul_zero])]
  simp_rw [ht]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_eq_add_neg]

/-- The total diagonal, after subtracting the actual inward current, is bounded by
the weighted energy. The value of the trial function at the third terminal is free. -/
theorem total_response_sub_current_le_weightedEnergy (a b : E → V)
    (alpha beta : V) (hbeta : beta ≠ alpha) (side : E → Bool)
    (hc : (supportGraph a b).Preconnected) (phi : V → ℝ)
    (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hp : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0)
    (f : SplitVertex alpha → ℝ) (hf0 : f (.inr false) = 0)
    (hf1 : f (.inr true) = 1) :
    let A := fun e => splitEndpoint alpha side (a e) e
    let B := fun e => splitEndpoint alpha side (b e) e
    let Phi := fun x => phi (collapse alpha x)
    responseEntry A B (splitTerminals alpha beta hbeta)
        (split_terminal_reachable a b alpha beta hbeta side hc) 1 1 -
      (-laplacian A B Phi (.inr true)) ≤
        weightedEnergy A B (fun x => 1 - Phi x) f := by
  intro A B Phi
  let r := splitTerminals alpha beta hbeta
  let hR := split_terminal_reachable a b alpha beta hbeta side hc
  let u := fun x => (1 - Phi x) * f x
  have hPhi := Plane.split_pullback_harmonic a b alpha beta hbeta side phi hp
  have he := ground_energy_eq_current A B r (splitTerminals_injective alpha beta hbeta)
    Phi f hp0 hp0 hp1 hf0 hf1 hPhi
  have hu (i : Fin 3) : u (r i) = responseBasis A B r hR 1 (r i) := by
    rw [responseBasis_terminal A B r (splitTerminals_injective alpha beta hbeta) hR]
    fin_cases i
    · change (1 - phi alpha) * f (.inr false) = 0
      rw [hp0, hf0, mul_zero]
    · change (1 - phi alpha) * f (.inr true) = 1
      rw [hp0, hf1, sub_zero, mul_one]
    · change (1 - phi beta) * f (.inl ⟨beta, hbeta⟩) = 0
      rw [hp1, sub_self, zero_mul]
  have hmin : energy A B (responseBasis A B r hR 1) ≤ energy A B u := by
    rw [energy_eq_add_energy_sub_of_harmonic A B (terminalSet r) u
      (responseBasis A B r hR 1) (by
        intro x hx
        obtain ⟨i, rfl⟩ := (mem_terminalSet_iff r x).mp hx
        exact hu i) (responseBasis_harmonic A B r hR 1)]
    exact le_add_of_nonneg_right (energy_nonneg A B _)
  rw [← split_total_response_eq_energy a b alpha beta hbeta side hc] at hmin
  change responseEntry A B r hR 1 1 ≤ energy A B u at hmin
  change energy A B u = _ at he
  have hr1 : r 1 = Sum.inr true := rfl
  rw [hr1] at he
  rw [he] at hmin
  exact (sub_le_iff_le_add).mpr (by simpa only [sub_eq_add_neg] using hmin)

end FiniteAvalanches.Electrical.SplitStep
