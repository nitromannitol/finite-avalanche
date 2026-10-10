import FiniteAvalanches.Sandpile.Waves.RecurrentExtension
import FiniteAvalanches.Sandpile.Waves.Partition

/-! The inverse first-return map permutes terminal states. Source height three
then gives a literal bijection with recurrent configurations that trigger a
nonempty one-grain avalanche. Identifying the entire legal avalanche trace is
separate from this carrier and map bijection. -/

namespace FiniteAvalanches.Sandpile.Waves

open FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

/-- The next terminal state under the actual inverse wave dynamics. -/
def returnMap {N : ℕ} {o : FiniteWired.Active N} (h : TerminalState N o) : TerminalState N o :=
  ⟨inverse^[returnTime h] h.val, terminal_at_return h⟩

theorem return_map_injective {N : ℕ} {o : FiniteWired.Active N} :
    Function.Injective (@returnMap N o) := by
  intro h g he
  let p : ExcursionPoint N o := ⟨h, ⟨returnTime h - 1, by have hp := return_time_pos h; omega⟩⟩
  let q : ExcursionPoint N o := ⟨g, ⟨returnTime g - 1, by have hp := return_time_pos g; omega⟩⟩
  have hs : excursionState p = excursionState q := by
    apply waveEquiv.symm.injective
    change inverse (inverse^[returnTime h - 1] h.val) = inverse (inverse^[returnTime g - 1] g.val)
    rw [← Function.iterate_succ_apply' inverse (returnTime h - 1) h.val,
      ← Function.iterate_succ_apply' inverse (returnTime g - 1) g.val,
      show (returnTime h - 1).succ = returnTime h by have hp := return_time_pos h; omega,
      show (returnTime g - 1).succ = returnTime g by have hp := return_time_pos g; omega]
    exact congrArg Subtype.val he
  exact congrArg Sigma.fst (excursion_state_injective hs)

/-- The actual first-return permutation, proved from the excursion partition. -/
def returnEquiv {N : ℕ} {o : FiniteWired.Active N} : TerminalState N o ≃ TerminalState N o :=
  Equiv.ofBijective returnMap (Finite.injective_iff_bijective.mp return_map_injective)

abbrev SourceThree (N : ℕ) (o : FiniteWired.Active N) :=
  {η : FiniteWired.Recurrent N // η.val o = 3}

def terminalToSourceThree {N : ℕ} {o : FiniteWired.Active N} (h : TerminalState N o) : SourceThree N o :=
  ⟨⟨sourceExtension 3 h.val.val, (source_extension_recurrent_iff h.val.property 3).mpr (by
      have hh := h.property
      unfold terminal at hh
      norm_num
      omega)⟩, by simp [sourceExtension]⟩

def sourceThreeToTerminal {N : ℕ} {o : FiniteWired.Active N} (η : SourceThree N o) : TerminalState N o := by
  let h : Punctured N o := ⟨restrictOff o η.val.val, restrict_recurrent_allowed o η.val.property⟩
  refine ⟨h, ?_⟩
  have hh := (source_extension_recurrent_iff h.property (η.val.val o)).mp
    (show FiniteWired.recurrent (sourceExtension (η.val.val o) h.val) by
      rw [source_extension_restrict]; exact η.val.property)
  rw [η.property] at hh
  unfold terminal
  norm_num at hh
  omega

/-- Exactly the recurrent configurations whose source has height three. -/
def sourceThreeEquiv {N : ℕ} {o : FiniteWired.Active N} : TerminalState N o ≃ SourceThree N o where
  toFun := terminalToSourceThree
  invFun := sourceThreeToTerminal
  left_inv h := Subtype.ext (Subtype.ext (restrict_source_extension 3 h.val.val))
  right_inv η := by
    apply Subtype.ext
    apply Subtype.ext
    change sourceExtension 3 (restrictOff o η.val.val) = η.val.val
    simpa only [η.property] using source_extension_restrict o η.val.val

/-- An inverse excursion maps to its source-three recurrent starting configuration. -/
def excursionPredecessorEquiv {N : ℕ} {o : FiniteWired.Active N} : TerminalState N o ≃ SourceThree N o :=
  returnEquiv.trans sourceThreeEquiv

theorem forward_return_map {N : ℕ} {o : FiniteWired.Active N} (h : TerminalState N o) :
    forward^[returnTime h] (returnMap h).val = h.val :=
  (Function.LeftInverse.iterate forward_inverse (returnTime h)) h.val

theorem not_terminal_inside_forward_excursion {N : ℕ} {o : FiniteWired.Active N}
    (h : TerminalState N o) {j : ℕ} (hj : 0 < j) (hjr : j < returnTime h) :
    ¬terminal (forward^[j] (returnMap h).val) := by
  change ¬terminal (forward^[j] (inverse^[returnTime h] h.val))
  rw [forward_inverse_iterate_sub h.val j (returnTime h) hjr.le]
  exact not_terminal_before_return h (by omega) (by omega)

end
end FiniteAvalanches.Sandpile.Waves
