import FiniteAvalanches.Wilson.CyclePopping.TraceTermination
import FiniteAvalanches.Wilson.CyclePopping.SelectedPath

/-! First-hit loop erasure selects arrows of the terminal stack configuration. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open Quiver FiniteAvalanches.Wilson
open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {A : V → Type*}

/-- A chronological stack walk hits the roots, and its first-hit loop erasure
uses exactly the arrows selected by the terminal pop configuration. -/
theorem terminal_selects_firstHit_erasure (R : Set V) (head : (v : V) → A v → V)
    (σ : Stacks A) (k t : Cursor V)
    (hrun : Relation.ReflTransGen (pop_step R head σ) k t)
    (ht : terminal R head σ t) (x : V) :
    letI : Quiver V := instructionQuiver head
    ∃ n, (instructionTrace head σ k x n).1 ∈ R ∧
      (∀ i < n, (instructionTrace head σ k x i).1 ∉ R) ∧
      selected (instructionArrowStacks head σ) t
        (loopErase (instructionTrace head σ k x n).2) := by
  letI : Quiver V := instructionQuiver head
  have hhit := instructionTrace_hits_of_terminal R head σ k t hrun ht x
  obtain ⟨n, hn, hfirst, hpop, hselected, _⟩ :=
    instructionTrace_firstHit_erasure R head σ k x hhit
  have hcontinue : Relation.ReflTransGen
      (pop_step R (fun _ s => s.1) (instructionArrowStacks head σ))
      (erasedCursor k (instructionTrace head σ k x n).2) t :=
    pop_run_continues_to_terminal R head σ hrun hpop ht
  exact ⟨n, hn, hfirst, selected_path_preserved R (instructionArrowStacks head σ)
    (loopErase (instructionTrace head σ k x n).2) hselected hn hcontinue⟩


/-- After the first loop-erased branch is attached to the roots, the remaining
legal pops still reach the same terminal cursor without touching that branch. -/
theorem terminal_after_firstHit_branch (R : Set V) (head : (v : V) → A v → V)
    (σ : Stacks A) (k t : Cursor V)
    (hrun : Relation.ReflTransGen (pop_step R head σ) k t)
    (ht : terminal R head σ t) (x : V) :
    letI : Quiver V := instructionQuiver head
    ∃ n, (instructionTrace head σ k x n).1 ∈ R ∧
      (∀ i < n, (instructionTrace head σ k x i).1 ∉ R) ∧
      let p := loopErase (instructionTrace head σ k x n).2
      let l := erasedCursor k (instructionTrace head σ k x n).2
      selected (instructionArrowStacks head σ) l p ∧
      Relation.ReflTransGen (pop_step R head σ) k l ∧
      Relation.ReflTransGen (pop_step (R ∪ {v | v ∈ p.vertices}) head σ) l t ∧
      terminal (R ∪ {v | v ∈ p.vertices}) head σ t := by
  letI : Quiver V := instructionQuiver head
  have hhit := instructionTrace_hits_of_terminal R head σ k t hrun ht x
  obtain ⟨n, hn, hfirst, hpop, hselected, _⟩ :=
    instructionTrace_firstHit_erasure R head σ k x hhit
  have hcontinue := pop_run_continues_to_terminal R head σ hrun hpop ht
  have hcontinue' : Relation.ReflTransGen
      (pop_step R (fun _ s => s.1) (instructionArrowStacks head σ))
      (erasedCursor k (instructionTrace head σ k x n).2) t := hcontinue
  have hroots := selected_path_pop_run_with_roots R (instructionArrowStacks head σ)
    (loopErase (instructionTrace head σ k x n).2) hselected hn hcontinue'
  refine ⟨n, hn, hfirst, hselected, hpop, hroots, ?_⟩
  exact terminal_mono_roots R _ head σ t Set.subset_union_left ht

end
end FiniteAvalanches.Wilson.CyclePopping
