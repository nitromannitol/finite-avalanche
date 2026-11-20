import FiniteAvalanches.Wilson.Lattice.HistoryArrows
import FiniteAvalanches.Wilson.CyclePopping.RootOrbits

/-! Rootward behavior determined by finite loop-erased branch histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open Quiver FiniteAvalanches.Wilson FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- A root-ending realized history is closed under its selected nonroot
successors. -/
theorem BranchHistory.Realizes.successor_mem_roots
    (head : V → FiniteWired.Direction → V) (x : ℕ → V) (R : Set V)
    (n : ℕ) (h : BranchHistory n) (a : V → FiniteWired.Direction)
    (hend : BranchHistory.EndsInRoots head x R n h)
    (ha : BranchHistory.Realizes head x a n h) :
    ∀ v ∈ branchHistoryRoots head x R n h, v ∉ R →
      head v (a v) ∈ branchHistoryRoots head x R n h := by
  letI : Quiver V := instructionQuiver head
  induction n with
  | zero => intro v hv hvR; exact (hvR hv).elim
  | succ n ih =>
    change BranchHistory.EndsInRoots head x R n h.1 ∧ _ at hend
    change BranchHistory.Realizes head x a n h.1 ∧ _ at ha
    intro v hv hvR
    change v ∈ branchHistoryRoots head x R n h.1 ∪
      {v | v ∈ (loopErase (historyTrace head (x n) h.2).2).vertices} at hv
    change head v (a v) ∈ branchHistoryRoots head x R n h.1 ∪
      {v | v ∈ (loopErase (historyTrace head (x n) h.2).2).vertices}
    rcases hv with hv | hv
    · exact Or.inl (ih h.1 hend.1 ha.1 v hv hvR)
    · change v ∈ (loopErase (historyTrace head (x n) h.2).2).vertices at hv
      by_cases hlast : v = (historyTrace head (x n) h.2).1
      · exact Or.inl (ih h.1 hend.1 ha.1 v (hlast.symm ▸ hend.2) hvR)
      · have hdep : v ∈ departures (loopErase (historyTrace head (x n) h.2).2) := by
          have hm : v ∈ departures (loopErase (historyTrace head (x n) h.2).2) ++
              [(historyTrace head (x n) h.2).1] := by
            simpa only [departures, Path.dropLast_append_end_eq] using hv
          rcases List.mem_append.mp hm with hm | hm
          · exact hm
          · exact (hlast (List.mem_singleton.mp hm)).elim
        have hf := selected_follows
          (instructionArrowStacks head (fun v _ => a v)) (fun _ => 0)
          (loopErase (historyTrace head (x n) h.2).2) ha.2
        change follows (fun v => head v (a v)) _ at hf
        exact Or.inr (follows_successor_mem _ _ hf hdep)

/-- Two rootward maps that agree on a closed set have the same first root for
every vertex of that set. -/
theorem firstRoot_eq_of_agree_on_closed (R U : Set V) (f g : V → V)
    (hf : ∀ v, ∃ n, f^[n] v ∈ R) (hg : ∀ v, ∃ n, g^[n] v ∈ R)
    (hclosed : ∀ v ∈ U, v ∉ R → f v ∈ U)
    (hagree : ∀ v ∈ U, v ∉ R → f v = g v)
    {v : V} (hv : v ∈ U) : firstRoot R f hf v = firstRoot R g hg v := by
  let t := Nat.find (hf v)
  have hiter : ∀ i ≤ t, f^[i] v = g^[i] v ∧ f^[i] v ∈ U := by
    intro i hi
    induction i with
    | zero => exact ⟨rfl, hv⟩
    | succ i ih =>
      obtain ⟨he, hU⟩ := ih (Nat.le_trans (Nat.le_succ i) hi)
      have hn : f^[i] v ∉ R := Nat.find_min (hf v) (lt_of_lt_of_le (Nat.lt_succ_self i) hi)
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact ⟨(hagree _ hU hn).trans (congrArg g he), hclosed _ hU hn⟩
  have hgt : Nat.find (hg v) ≤ t := by
    apply Nat.find_min'
    rw [← (hiter t le_rfl).1]
    exact Nat.find_spec (hf v)
  have htg : t ≤ Nat.find (hg v) := by
    apply Nat.le_of_not_gt
    intro hlt
    have hmem : g^[Nat.find (hg v)] v ∈ R := Nat.find_spec (hg v)
    rw [← (hiter _ (Nat.le_of_lt hlt)).1] at hmem
    exact Nat.find_min (hf v) hlt hmem
  have he : Nat.find (hg v) = t := Nat.le_antisymm hgt htg
  unfold firstRoot
  rw [he]
  exact (hiter t le_rfl).1

/-- Any two good arrow assignments realizing a root-ending history have the
same first root at each vertex attached in that history. -/
theorem BranchHistory.Realizes.firstRoot_eq
    (head : V → FiniteWired.Direction → V) (x : ℕ → V) (R : Set V)
    (n : ℕ) (h : BranchHistory n) (a b : V → FiniteWired.Direction)
    (hend : BranchHistory.EndsInRoots head x R n h)
    (ha : BranchHistory.Realizes head x a n h)
    (hb : BranchHistory.Realizes head x b n h)
    (hita : ∀ v, ∃ i, (fun v => head v (a v))^[i] v ∈ R)
    (hitb : ∀ v, ∃ i, (fun v => head v (b v))^[i] v ∈ R)
    {v : V} (hv : v ∈ branchHistoryRoots head x R n h) :
    firstRoot R (fun v => head v (a v)) hita v =
      firstRoot R (fun v => head v (b v)) hitb v := by
  apply firstRoot_eq_of_agree_on_closed R (branchHistoryRoots head x R n h)
    (fun v => head v (a v)) (fun v => head v (b v)) hita hitb
    (BranchHistory.Realizes.successor_mem_roots head x R n h a hend ha) ?_ hv
  intro u hu huR
  rw [BranchHistory.Realizes.eq_of_mem_roots head x R n h a b hend ha hb hu huR]

end
end FiniteAvalanches.Wilson.Lattice
