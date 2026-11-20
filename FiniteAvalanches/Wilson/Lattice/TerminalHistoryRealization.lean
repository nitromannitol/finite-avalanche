import FiniteAvalanches.Wilson.Lattice.HistoryArrows
import FiniteAvalanches.Wilson.CyclePopping.StackExploration

/-! Terminal stack outputs realize successful finite Wilson histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A terminal direction stack realizes every branch of a successful finite prefix. -/
theorem terminal_realizes_branchHistory
    (head : V → FiniteWired.Direction → V) (R : Set V) (x : ℕ → V) (k t : Cursor V)
    (N n : ℕ) (σ : V × ℕ → FiniteWired.Direction)
    (hrun : Relation.ReflTransGen (pop_step R head (fun v i => σ (v, i))) k t)
    (ht : terminal R head (fun v i => σ (v, i)) t)
    (h : ∀ i < n, (boundedBranchHistory head x R k N σ (i + 1)).2.1 < N) :
    BranchHistory.Realizes head x (fun v => σ (v, t v)) n
      (boundedBranchHistory head x R k N σ n) := by
  let a := boundedBranchHistory head x R k N σ n
  let U := branchHistoryRoots head x R n a
  let j := branchHistoryErasedCursor head x k n a
  have hexact := (stackExplore_eq_historyErasedCursor head x R k N n σ h).1
  obtain ⟨U', j', hexplore, _, _, _, hcontinue, _⟩ :=
    stackExplore_of_terminal R head (fun v i => σ (v, i)) k t hrun ht ((List.range n).map x)
  rw [hexplore, Option.some.injEq, Prod.mk.injEq] at hexact
  have heU : U' = U := hexact.1
  have hej : j' = j := hexact.2
  have hc : ∀ v ∈ U, j v = t v := by
    intro v hv
    rw [← heU] at hv
    rw [← hej]
    exact (pop_run_root_cursor U' head (fun v i => σ (v, i)) hcontinue hv).symm
  have hs : BranchHistory.Selected head x σ j n a :=
    branchHistory_selected_of_hits head x R k N n σ h
  have hs' := BranchHistory.Selected.congr head x R σ j t n a hs hc
  exact BranchHistory.Selected.top head x σ n a t hs'

end
end FiniteAvalanches.Wilson.Lattice
