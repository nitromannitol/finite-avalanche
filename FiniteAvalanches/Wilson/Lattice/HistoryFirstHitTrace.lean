import FiniteAvalanches.Wilson.Lattice.HistoryErasedCursor

/-! First-hit stack traces reconstructed from stopped branch histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open Quiver FiniteAvalanches.Wilson FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- A successful bounded branch records the exact first-hit trace even when
the two starting cursors differ at already attached roots. -/
theorem firstHitTrace_eq_history_of_boundedHit
    (head : V → FiniteWired.Direction → V) (R : Set V) (x : V)
    (k l : Cursor V) (N : ℕ) (σ : V × ℕ → FiniteWired.Direction)
    (hcursor : ∀ v, v ∉ R → k v = l v)
    (h : boundedWordHit head R x l N (readingLetter head x l σ) < N) :
    letI : Quiver V := instructionQuiver head
    let p := stoppedDirectionHistory (boundedWordHit head R x l N) (readingLetter head x l σ)
    ∃ hh : ∃ i, (instructionTrace head (fun v j => σ (v, j)) k x i).1 ∈ R,
      instructionTrace head (fun v j => σ (v, j)) k x (Nat.find hh) = historyTrace head x p := by
  letI : Quiver V := instructionQuiver head
  let w := readingLetter head x l σ
  let t := boundedWordHit head R x l N w
  let p := stoppedDirectionHistory (boundedWordHit head R x l N) w
  have hw := instructionTrace_eq_read_driver head x l σ
  have hhit : (instructionTrace head (fun v i => σ (v, i)) l x t).1 ∈ R := by
    rw [(hw t).1]
    exact boundedWordHit_mem_of_lt head R x l N w h
  have havoid : ∀ i < t, (instructionTrace head (fun v j => σ (v, j)) l x i).1 ∉ R := by
    intro i hi
    rw [(hw i).1]
    exact boundedWordHit_avoids head R x l N w i hi
  have heq := instructionTrace_eq_until_roots head R x l k σ t
    (fun v hv => (hcursor v hv).symm) havoid
  have hk : ∃ i, (instructionTrace head (fun v j => σ (v, j)) k x i).1 ∈ R :=
    ⟨t, (congrArg Sigma.fst heq) ▸ hhit⟩
  have hfind : Nat.find hk = t := by
    apply Nat.le_antisymm (Nat.find_min' hk ((congrArg Sigma.fst heq) ▸ hhit))
    apply Nat.le_of_not_gt
    intro hi
    have ht := instructionTrace_eq_until_roots head R x l k σ (Nat.find hk)
      (fun v hv => (hcursor v hv).symm) (fun i hi' => havoid i (lt_trans hi' hi))
    exact havoid _ hi ((congrArg Sigma.fst ht).symm ▸ Nat.find_spec hk)
  have hp : historyTrace head x p = instructionTrace head (fun v i => σ (v, i)) l x t :=
    historyTrace_stoppedDirectionHistory head x l (boundedWordHit head R x l N) σ
  refine ⟨hk, ?_⟩
  rw [hfind, ← heq, ← hp]

end
end FiniteAvalanches.Wilson.Lattice
