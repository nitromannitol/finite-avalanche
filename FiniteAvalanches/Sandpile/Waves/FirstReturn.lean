import FiniteAvalanches.Sandpile.Waves.Cycles
import Mathlib.GroupTheory.Perm.Finite

/-! Finite legal termination supplies the genuine inverse return dynamics.
The return time is positive; zero belongs to each excursion but is not a return. -/

namespace FiniteAvalanches.Sandpile.Waves

open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

theorem exists_inverse_period {N : ℕ} {o : FiniteWired.Active N} :
    ∃ k : ℕ, 0 < k ∧ inverse^[k] = (@id (Punctured N o)) := by
  obtain ⟨k, hk, he⟩ := (isOfFinOrder_of_finite (waveEquiv.symm : Equiv.Perm (Punctured N o))).exists_pow_eq_one
  refine ⟨k, hk, ?_⟩
  have hh := congrArg (fun e : Equiv.Perm (Punctured N o) => (e : Punctured N o → Punctured N o)) he
  simpa only [Equiv.Perm.coe_pow, Equiv.Perm.coe_one, inverse] using hh

theorem inverse_orbit_reaches_terminal {N : ℕ} {o : FiniteWired.Active N} (h : Punctured N o) :
    ∃ j : ℕ, terminal (inverse^[j] h) := by
  obtain ⟨n, _, hn⟩ := forward_orbit_reaches_terminal h
  obtain ⟨k, hk, hp⟩ := exists_inverse_period (N := N) (o := o)
  have hkn : n ≤ k * (n + 1) := by nlinarith
  have hperiod : inverse^[k * (n + 1)] h = h := by
    rw [Function.iterate_mul, hp]
    simp
  refine ⟨k * (n + 1) - n, ?_⟩
  have he : inverse^[k * (n + 1) - n] h = forward^[n] h := by
    apply (waveEquiv.symm.injective.iterate n)
    change inverse^[n] (inverse^[k * (n + 1) - n] h) = inverse^[n] (forward^[n] h)
    rw [← Function.iterate_add_apply, show n + (k * (n + 1) - n) = k * (n + 1) by omega]
    rw [hperiod, (Function.LeftInverse.iterate inverse_forward n) h]
  rw [he]
  exact hn

abbrev TerminalState (N : ℕ) (o : FiniteWired.Active N) := {h : Punctured N o // terminal h}

theorem exists_inverse_return {N : ℕ} {o : FiniteWired.Active N} (h : TerminalState N o) :
    ∃ n : ℕ, 0 < n ∧ terminal (inverse^[n] h.val) := by
  obtain ⟨k, hk, hp⟩ := exists_inverse_period (N := N) (o := o)
  exact ⟨k, hk, by rw [hp]; exact h.property⟩

/-- The first strictly positive inverse return to the source-extension locus. -/
def returnTime {N : ℕ} {o : FiniteWired.Active N} (h : TerminalState N o) : ℕ :=
  Nat.find (exists_inverse_return h)

theorem return_time_pos {N : ℕ} {o : FiniteWired.Active N} (h : TerminalState N o) :
    0 < returnTime h := (Nat.find_spec (exists_inverse_return h)).1

theorem terminal_at_return {N : ℕ} {o : FiniteWired.Active N} (h : TerminalState N o) :
    terminal (inverse^[returnTime h] h.val) := (Nat.find_spec (exists_inverse_return h)).2

theorem not_terminal_before_return {N : ℕ} {o : FiniteWired.Active N}
    (h : TerminalState N o) {j : ℕ} (hj : 0 < j) (hjr : j < returnTime h) :
    ¬terminal (inverse^[j] h.val) := by
  intro ht
  have hle := Nat.find_min' (exists_inverse_return h) ⟨hj, ht⟩
  change returnTime h ≤ j at hle
  omega

/-- A complete inverse excursion, starting at a terminal state and excluding its next return. -/
abbrev ExcursionPoint (N : ℕ) (o : FiniteWired.Active N) :=
  (h : TerminalState N o) × Fin (returnTime h)

def excursionState {N : ℕ} {o : FiniteWired.Active N} (p : ExcursionPoint N o) : Punctured N o :=
  inverse^[p.2.val] p.1.val

end
end FiniteAvalanches.Sandpile.Waves
