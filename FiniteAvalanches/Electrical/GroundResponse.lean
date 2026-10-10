import FiniteAvalanches.Electrical.Response
import FiniteAvalanches.Electrical.SplitResponse

/-! Ground-state cancellation against the proved Dirichlet response minimum. -/

namespace FiniteAvalanches.Electrical

open scoped BigOperators Classical

variable {V E : Type*} [Fintype V] [Fintype E]

theorem voltage_energy_eq_response (a b : E → V) (r : Fin 3 → V)
    (hr : Function.Injective r)
    (hB : ∀ x, ∃ y ∈ terminalSet r, (supportGraph a b).Reachable x y)
    (phi : V → ℝ) (hp0 : phi (r 0) = 0) (hp1 : phi (r 1) = 0) (hp2 : phi (r 2) = 1)
    (hp : ∀ x, x ∉ terminalSet r → laplacian a b phi x = 0) :
    energy a b phi = -responseEntry a b r hB 0 2 - responseEntry a b r hB 1 2 := by
  let t : Fin 3 → ℝ := ![0, 0, 1]
  let h : V → ℝ := fun x => ∑ j, t j * responseBasis a b r hB j x
  have hs := response_potential_spec a b r hr hB t
  have ht (i : Fin 3) : phi (r i) = t i := by
    fin_cases i
    · exact hp0
    · exact hp1
    · exact hp2
  have he : phi = h := eq_of_harmonic_boundary a b (terminalSet r) hB phi h
    (fun x hx => by
      obtain ⟨i, hi⟩ := (mem_terminalSet_iff r x).mp hx
      exact (congrArg phi hi).symm.trans
        ((ht i).trans ((hs.1 i).symm.trans (congrArg h hi)))) hp hs.2
  rw [he, three_terminal_response_energy a b r hr hB t]
  simp [t, sub_eq_add_neg]

/-- Cancellation of the full background energy, deriving the response bound. -/
theorem ground_response_upper_bound (a b : E → V) (r : Fin 3 → V)
    (hr : Function.Injective r)
    (hB : ∀ x, ∃ y ∈ terminalSet r, (supportGraph a b).Reachable x y)
    (phi f : V → ℝ) (hp0 : phi (r 0) = 0) (hp1 : phi (r 1) = 0)
    (hp2 : phi (r 2) = 1) (hf0 : f (r 0) = 0) (hf1 : f (r 1) = 1)
    (hp : ∀ x, x ∉ terminalSet r → laplacian a b phi x = 0) :
    -responseEntry a b r hB 0 1 ≤ weightedEnergy a b (fun x => 1 - phi x) f := by
  let t : V → ℝ := fun x => (1 / 2 : ℝ) + (1 - phi x) * (f x - 1 / 2)
  have ht (i : Fin 3) : t (r i) = (![0, 1, (1 / 2 : ℝ)] : Fin 3 → ℝ) i := by
    fin_cases i
    · change t (r 0) = 0
      dsimp only [t]; rw [hp0, hf0]; ring
    · change t (r 1) = 1
      dsimp only [t]; rw [hp1, hf1]; ring
    · change t (r 2) = 1 / 2
      dsimp only [t]; rw [hp2]; ring
  have hmin := three_terminal_response_minimum a b r hr hB ![0, 1, (1 / 2 : ℝ)] t ht
  change -responseEntry a b r hB 0 1 * (0 - 1) ^ 2 +
    -responseEntry a b r hB 0 2 * (0 - (1 / 2 : ℝ)) ^ 2 +
    -responseEntry a b r hB 1 2 * (1 - (1 / 2 : ℝ)) ^ 2 ≤ energy a b t at hmin
  have hph (x : V) (hx0 : x ≠ r 0) (hx1 : x ≠ r 1) (hx2 : x ≠ r 2) :
      laplacian a b phi x = 0 := by
    apply hp x
    intro hx
    obtain ⟨i, hi⟩ := (mem_terminalSet_iff r x).mp hx
    fin_cases i
    · exact hx0 hi.symm
    · exact hx1 hi.symm
    · exact hx2 hi.symm
  have h01 : r 0 ≠ r 1 := fun he => (by decide : (0 : Fin 3) ≠ 1) (hr he)
  have hground := ground_trial_energy_of_voltage a b phi f (r 0) (r 1) (r 2)
    h01 hp0 hp1 hp2 hf0 hf1 hph
  have he := voltage_energy_eq_response a b r hr hB phi hp0 hp1 hp2 hp
  change energy a b t = _ at hground
  rw [hground, he] at hmin
  norm_num at hmin
  linarith only [hmin]

end FiniteAvalanches.Electrical
