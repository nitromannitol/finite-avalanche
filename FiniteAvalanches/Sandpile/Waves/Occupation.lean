import FiniteAvalanches.Sandpile.Waves.Partition

/-! Unweighted finite occupation is a direct sum transport through the actual
excursion bijection. Multiplication by the manuscript's common mass preserves
this identity; no probability normalization of the punctured space is used. -/

namespace FiniteAvalanches.Sandpile.Waves

open scoped Classical
noncomputable section

instance puncturedFintype {N : ℕ} {o : FiniteWired.Active N} : Fintype (Punctured N o) :=
  Fintype.ofFinite _

instance terminalStateFintype {N : ℕ} {o : FiniteWired.Active N} : Fintype (TerminalState N o) :=
  Fintype.ofFinite _

/-- The exact deterministic occupation sum, retaining both excursion endpoints' conventions. -/
theorem sum_inverse_excursions {N : ℕ} {o : FiniteWired.Active N} (q : Punctured N o → ℝ) :
    (∑ h : TerminalState N o, ∑ j : Fin (returnTime h), q (inverse^[j.val] h.val)) =
      ∑ x : Punctured N o, q x := by
  calc
    _ = ∑ p : ExcursionPoint N o, q (excursionState p) :=
      (Fintype.sum_sigma (fun p : ExcursionPoint N o => q (excursionState p))).symm
    _ = _ := excursionEquiv.sum_comp q

end
end FiniteAvalanches.Sandpile.Waves
