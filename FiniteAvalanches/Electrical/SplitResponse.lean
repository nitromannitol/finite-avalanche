import FiniteAvalanches.Electrical.SplitTerminal
import FiniteAvalanches.Electrical.Response
import Mathlib.Tactic.FinCases

/-! Response construction on the split-terminal carrier. -/

namespace FiniteAvalanches.Electrical

open scoped BigOperators Classical

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The two copies of `alpha` followed by the unchanged terminal `beta`. -/
def splitTerminals (alpha beta : V) (hbeta : beta ≠ alpha) : Fin 3 → SplitVertex alpha :=
  ![Sum.inr false, Sum.inr true, Sum.inl ⟨beta, hbeta⟩]

omit [Fintype V] in
theorem splitTerminals_injective (alpha beta : V) (hbeta : beta ≠ alpha) :
    Function.Injective (splitTerminals alpha beta hbeta) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [splitTerminals] at hij ⊢

omit [Fintype V] [Fintype E] in
/-- The component condition is proved for the actual split network. -/
theorem split_terminal_reachable (a b : E → V) (alpha beta : V)
    (hbeta : beta ≠ alpha) (side : E → Bool) (hc : (supportGraph a b).Preconnected) :
    ∀ x, ∃ y ∈ terminalSet (splitTerminals alpha beta hbeta),
      (supportGraph (fun e => splitEndpoint alpha side (a e) e)
        (fun e => splitEndpoint alpha side (b e) e)).Reachable x y := by
  intro x
  obtain ⟨k, hk⟩ := split_reachable_terminal a b alpha side hc x
  cases k with
  | false => exact ⟨Sum.inr false, mem_terminalSet (splitTerminals alpha beta hbeta) 0, hk⟩
  | true => exact ⟨Sum.inr true, mem_terminalSet (splitTerminals alpha beta hbeta) 1, hk⟩

theorem eq_of_harmonic_boundary (a b : E → V) (B : Finset V)
    (hB : ∀ x, ∃ y ∈ B, (supportGraph a b).Reachable x y) (f g : V → ℝ)
    (hfg : ∀ x ∈ B, f x = g x)
    (hf : ∀ x, x ∉ B → laplacian a b f x = 0)
    (hg : ∀ x, x ∉ B → laplacian a b g x = 0) : f = g := by
  apply sub_eq_zero.mp
  apply eq_zero_of_harmonic a b B hB
  · intro x hx; exact sub_eq_zero.mpr (hfg x hx)
  · intro x hx; rw [laplacian_sub, hf x hx, hg x hx, sub_self]

/-- Rejoining the two zero-valued copies preserves the original voltage energy. -/
theorem split_voltage_energy_eq_response (a b : E → V) (alpha beta : V)
    (hbeta : beta ≠ alpha) (side : E → Bool) (hc : (supportGraph a b).Preconnected)
    (phi : V → ℝ) (hpa : phi alpha = 0) (hpb : phi beta = 1)
    (hp : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0) :
    let A := fun e => splitEndpoint alpha side (a e) e
    let B := fun e => splitEndpoint alpha side (b e) e
    let r := splitTerminals alpha beta hbeta
    let hR := split_terminal_reachable a b alpha beta hbeta side hc
    energy a b phi = -responseEntry A B r hR 0 2 - responseEntry A B r hR 1 2 := by
  intro A B r hR
  let t : Fin 3 → ℝ := ![0, 0, 1]
  let f : SplitVertex alpha → ℝ := fun x => ∑ j, t j * responseBasis A B r hR j x
  let p : SplitVertex alpha → ℝ := fun x => phi (collapse alpha x)
  have hs := response_potential_spec A B r (splitTerminals_injective alpha beta hbeta) hR t
  have hpt (i : Fin 3) : p (r i) = t i := by
    fin_cases i
    · exact hpa
    · exact hpa
    · exact hpb
  have hph : ∀ x, x ∉ terminalSet r → laplacian A B p x = 0 := by
    intro x hx
    rcases x with x | k
    · rw [split_laplacian_inl]
      apply hp x.val x.property
      intro hxb
      have hmem := mem_terminalSet r 2
      have hxe : r 2 = Sum.inl x := by
        apply congrArg Sum.inl
        exact Subtype.ext hxb.symm
      exact hx (hxe ▸ hmem)
    · cases k with
      | false => exact (hx (mem_terminalSet r 0)).elim
      | true => exact (hx (mem_terminalSet r 1)).elim
  have hpf : p = f := eq_of_harmonic_boundary A B (terminalSet r) hR p f
    (fun x hx => by
      obtain ⟨i, hi⟩ := (mem_terminalSet_iff r x).mp hx
      exact (congrArg p hi).symm.trans
        ((hpt i).trans ((hs.1 i).symm.trans (congrArg f hi)))) hph hs.2
  rw [← split_energy_pullback a b alpha side phi]
  change energy A B p = _
  rw [hpf, three_terminal_response_energy A B r (splitTerminals_injective alpha beta hbeta) hR t]
  simp [t, sub_eq_add_neg]

end FiniteAvalanches.Electrical
