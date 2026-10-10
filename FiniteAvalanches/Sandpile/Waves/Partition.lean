import FiniteAvalanches.Sandpile.Waves.FirstReturn

/-! Every actual punctured state occurs in exactly one complete inverse excursion.
This is the deterministic bijection behind `fv:exact-occupation`; no measure is
normalized or introduced here. -/

namespace FiniteAvalanches.Sandpile.Waves

open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

theorem forward_inverse_iterate_sub {N : ℕ} {o : FiniteWired.Active N}
    (x : Punctured N o) (i j : ℕ) (hij : i ≤ j) :
    forward^[i] (inverse^[j] x) = inverse^[j - i] x := by
  calc
    forward^[i] (inverse^[j] x) = forward^[i] (inverse^[i] (inverse^[j - i] x)) := by
      rw [← Function.iterate_add_apply, show i + (j - i) = j by omega]
    _ = _ := (Function.LeftInverse.iterate forward_inverse i) _

theorem inverse_forward_iterate_sub {N : ℕ} {o : FiniteWired.Active N}
    (x : Punctured N o) (i j : ℕ) (hij : i ≤ j) :
    inverse^[i] (forward^[j] x) = forward^[j - i] x := by
  calc
    inverse^[i] (forward^[j] x) = inverse^[i] (forward^[i] (forward^[j - i] x)) := by
      rw [← Function.iterate_add_apply, show i + (j - i) = j by omega]
    _ = _ := (Function.LeftInverse.iterate inverse_forward i) _

theorem excursion_state_injective {N : ℕ} {o : FiniteWired.Active N} :
    Function.Injective (@excursionState N o) := by
  rintro ⟨h, i⟩ ⟨g, j⟩ he
  change inverse^[i.val] h.val = inverse^[j.val] g.val at he
  have hi : i.val = j.val := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hij | hji
    · have hh := congrArg (forward^[i.val]) he
      rw [forward_inverse_iterate_sub h.val i.val i.val le_rfl,
        forward_inverse_iterate_sub g.val i.val j.val hij.le] at hh
      simp only [Nat.sub_self, Function.iterate_zero, id_eq] at hh
      have ht : terminal (inverse^[j.val - i.val] g.val) := hh ▸ h.property
      exact not_terminal_before_return g (by omega) (by have hj := j.isLt; omega) ht
    · have hh := congrArg (forward^[j.val]) he
      rw [forward_inverse_iterate_sub h.val j.val i.val hji.le,
        forward_inverse_iterate_sub g.val j.val j.val le_rfl] at hh
      simp only [Nat.sub_self, Function.iterate_zero, id_eq] at hh
      have ht : terminal (inverse^[i.val - j.val] h.val) := hh.symm ▸ g.property
      exact not_terminal_before_return h (by omega) (by have hi := i.isLt; omega) ht
  have hg : h = g := by
    apply Subtype.ext
    have hh := congrArg (forward^[i.val]) he
    rw [← hi, forward_inverse_iterate_sub h.val i.val i.val le_rfl,
      forward_inverse_iterate_sub g.val i.val i.val le_rfl] at hh
    simpa using hh
  subst g
  exact congrArg (fun k : Fin (returnTime h) => (⟨h, k⟩ : ExcursionPoint N o)) (Fin.ext hi)

theorem excursion_state_surjective {N : ℕ} {o : FiniteWired.Active N} :
    Function.Surjective (@excursionState N o) := by
  intro x
  have hex : ∃ n : ℕ, terminal (forward^[n] x) := by
    obtain ⟨n, _, ht⟩ := forward_orbit_reaches_terminal x
    exact ⟨n, ht⟩
  let n := Nat.find hex
  let h : TerminalState N o := ⟨forward^[n] x, Nat.find_spec hex⟩
  have hnr : n < returnTime h := by
    by_contra hn
    have hrn : returnTime h ≤ n := by omega
    have ht := terminal_at_return h
    change terminal (inverse^[returnTime h] (forward^[n] x)) at ht
    rw [inverse_forward_iterate_sub x (returnTime h) n hrn] at ht
    have hmin := Nat.find_min' hex ht
    change n ≤ n - returnTime h at hmin
    have hpos := return_time_pos h
    omega
  refine ⟨⟨h, ⟨n, hnr⟩⟩, ?_⟩
  exact (Function.LeftInverse.iterate inverse_forward n) x

/-- The actual first-return excursion partition, including each starting state once. -/
def excursionEquiv {N : ℕ} {o : FiniteWired.Active N} : ExcursionPoint N o ≃ Punctured N o :=
  Equiv.ofBijective excursionState ⟨excursion_state_injective, excursion_state_surjective⟩

end
end FiniteAvalanches.Sandpile.Waves
