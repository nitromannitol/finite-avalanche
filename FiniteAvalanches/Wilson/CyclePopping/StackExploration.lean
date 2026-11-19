import FiniteAvalanches.Wilson.CyclePopping.TerminalTrace

/-! Finite Wilson exploration of the actual vertex instruction stacks. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open Quiver FiniteAvalanches.Wilson
open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {A : V → Type*}

/-- Explore one chronological stack walk up to its first root, erase its loops,
add the retained branch to the roots, and retain the actual pop cursor. -/
def stackStep (head : (v : V) → A v → V) (σ : Stacks A)
    (R : Set V) (k : Cursor V) (x : V) : Option (Set V × Cursor V) := by
  letI : Quiver V := instructionQuiver head
  exact if h : ∃ n, (instructionTrace head σ k x n).1 ∈ R then
    let p := loopErase (instructionTrace head σ k x (Nat.find h)).2
    some (R ∪ {v | v ∈ p.vertices}, erasedCursor k (instructionTrace head σ k x (Nat.find h)).2)
  else none

/-- Explore an ordered finite list against the same vertex stacks. -/
def stackExplore (head : (v : V) → A v → V) (σ : Stacks A) :
    Set V → Cursor V → List V → Option (Set V × Cursor V)
  | R, k, [] => some (R, k)
  | R, k, x :: xs => (stackStep head σ R k x).bind fun out =>
      stackExplore head σ out.1 out.2 xs

/-- A stack step attaches its query and preserves the same terminal pop result. -/
theorem stackStep_of_terminal (R : Set V) (head : (v : V) → A v → V)
    (σ : Stacks A) (k t : Cursor V)
    (hrun : Relation.ReflTransGen (pop_step R head σ) k t)
    (ht : terminal R head σ t) (x : V) :
    ∃ S l, stackStep head σ R k x = some (S, l) ∧ R ⊆ S ∧ x ∈ S ∧
      Relation.ReflTransGen (pop_step R head σ) k l ∧
      Relation.ReflTransGen (pop_step S head σ) l t ∧ terminal S head σ t := by
  letI : Quiver V := instructionQuiver head
  have hh := instructionTrace_hits_of_terminal R head σ k t hrun ht x
  obtain ⟨n, hn, hfirst, _, hpop, hcontinue, hterminal⟩ :=
    terminal_after_firstHit_branch R head σ k t hrun ht x
  have he : Nat.find hh = n := by
    apply Nat.le_antisymm (Nat.find_min' hh hn)
    apply Nat.le_of_not_gt
    intro hlt
    exact hfirst _ hlt (Nat.find_spec hh)
  subst n
  let p := loopErase (instructionTrace head σ k x (Nat.find hh)).2
  let l := erasedCursor k (instructionTrace head σ k x (Nat.find hh)).2
  let S : Set V := R ∪ {v | v ∈ p.vertices}
  refine ⟨S, l, ?_, Set.subset_union_left, Or.inr p.start_mem_vertices, hpop,
    hcontinue, hterminal⟩
  simp only [stackStep, dif_pos hh, S, p, l]

/-- Every finite ordered stack exploration terminates, covers all queried sites,
and leaves a legal continuation to the same terminal cursor. -/
theorem stackExplore_of_terminal (R : Set V) (head : (v : V) → A v → V)
    (σ : Stacks A) (k t : Cursor V)
    (hrun : Relation.ReflTransGen (pop_step R head σ) k t)
    (ht : terminal R head σ t) (L : List V) :
    ∃ S l, stackExplore head σ R k L = some (S, l) ∧ R ⊆ S ∧
      (∀ x ∈ L, x ∈ S) ∧ Relation.ReflTransGen (pop_step R head σ) k l ∧
      Relation.ReflTransGen (pop_step S head σ) l t ∧ terminal S head σ t := by
  induction L generalizing R k with
  | nil => exact ⟨R, k, rfl, Set.Subset.rfl, by simp, .refl, hrun, ht⟩
  | cons x xs ih =>
    obtain ⟨S, l, hs, hRS, hx, hkl, hlt, hSt⟩ := stackStep_of_terminal R head σ k t hrun ht x
    obtain ⟨T, m, htail, hST, hxs, hlm, hmt, hTt⟩ := ih S l hlt hSt
    refine ⟨T, m, ?_, hRS.trans hST, ?_, ?_, hmt, hTt⟩
    · simpa only [stackExplore, hs, Option.bind_some] using htail
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hST hx
      · exact hxs y hy
    · exact hkl.trans (pop_run_of_larger_roots R S head σ hRS hlm)


/-- If every vertex is queried, stack exploration reaches the unique terminal
cursor, independently of the query order. -/
theorem stackExplore_all_of_terminal (R : Set V) (head : (v : V) → A v → V)
    (σ : Stacks A) (k t : Cursor V)
    (hrun : Relation.ReflTransGen (pop_step R head σ) k t)
    (ht : terminal R head σ t) (L : List V) (hL : ∀ x, x ∈ L) :
    stackExplore head σ R k L = some (Set.univ, t) := by
  obtain ⟨S, l, hresult, _, hcover, _, hcontinue, hterminal⟩ :=
    stackExplore_of_terminal R head σ k t hrun ht L
  have hS : S = Set.univ := Set.eq_univ_of_forall (fun x => hcover x (hL x))
  have htl : terminal S head σ l := by
    intro c hc
    obtain ⟨v, hv⟩ := hc.nonempty
    exact hc.avoids_roots v hv (hS.symm ▸ Set.mem_univ v)
  have he : l = t := terminal_cursor_eq S head σ .refl hcontinue htl hterminal
  simpa only [hS, he] using hresult

end
end FiniteAvalanches.Wilson.CyclePopping
