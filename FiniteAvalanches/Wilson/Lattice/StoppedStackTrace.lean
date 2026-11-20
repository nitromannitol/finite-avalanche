import FiniteAvalanches.Wilson.CyclePopping.WordTrace
import FiniteAvalanches.Wilson.CyclePopping.RawStackStep
import FiniteAvalanches.Wilson.Lattice.BoundedStackHit

/-! Recovering raw Wilson branches from finite stopped direction histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open Quiver FiniteAvalanches.Wilson FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- The arrow-labeled trace determined by a finite direction history. -/
def historyTrace (head : V → FiniteWired.Direction → V) (x : V)
    (p : DirectionHistory) :
    letI : Quiver V := instructionQuiver head
    Σ y : V, Path x y :=
  wordTrace head x p.extend p.1

/-- The root set after attaching the chronological erasure of a recorded history. -/
def historyRoots (head : V → FiniteWired.Direction → V) (x : V)
    (R : Set V) (p : DirectionHistory) : Set V := by
  letI : Quiver V := instructionQuiver head
  exact R ∪ {v | v ∈ (loopErase (historyTrace head x p).2).vertices}

/-- A stopped history reconstructs the entire raw stack trace at its stopping time. -/
theorem historyTrace_stoppedDirectionHistory
    (head : V → FiniteWired.Direction → V) (x : V) (k : Cursor V)
    (t : WalkDriver → ℕ) (σ : V × ℕ → FiniteWired.Direction) :
    letI : Quiver V := instructionQuiver head
    historyTrace head x (stoppedDirectionHistory t (readingLetter head x k σ)) =
      instructionTrace head (fun v i => σ (v, i)) k x (t (readingLetter head x k σ)) := by
  letI : Quiver V := instructionQuiver head
  let w := readingLetter head x k σ
  let p := stoppedDirectionHistory t w
  have hp : ∀ i < p.1, p.extend i = w i := by
    intro i hi
    have hi' : i < t w := hi
    simp only [p, stoppedDirectionHistory, DirectionHistory.extend, dif_pos hi']
  have htrace := wordTrace_eq_of_prefix head x w p.extend p.1 hp
  exact htrace.trans (instructionTrace_eq_wordTrace head x k σ (t w)).symm

/-- On a first hit before the horizon, the raw Wilson step is recovered from
its finite stopped direction history. -/
theorem rawStackStep_eq_history_of_boundedHit
    (head : V → FiniteWired.Direction → V) (R : Set V) (x : V) (k : Cursor V)
    (N : ℕ) (σ : V × ℕ → FiniteWired.Direction)
    (h : boundedWordHit head R x k N (readingLetter head x k σ) < N) :
    let p := stoppedDirectionHistory (boundedWordHit head R x k N) (readingLetter head x k σ)
    rawStackStep head σ R k x = some (historyRoots head x R p, historyCursor head x k p) := by
  letI : Quiver V := instructionQuiver head
  let w := readingLetter head x k σ
  let t := boundedWordHit head R x k N w
  let p := stoppedDirectionHistory (boundedWordHit head R x k N) w
  have hw := instructionTrace_eq_read_driver head x k σ
  have hhit : (instructionTrace head (fun v i => σ (v, i)) k x t).1 ∈ R := by
    rw [(hw t).1]
    exact boundedWordHit_mem_of_lt head R x k N w h
  have hex : ∃ i, (instructionTrace head (fun v j => σ (v, j)) k x i).1 ∈ R := ⟨t, hhit⟩
  have hfind : Nat.find hex = t := by
    apply Nat.le_antisymm (Nat.find_min' hex hhit)
    apply Nat.le_of_not_gt
    intro hlt
    have hv := boundedWordHit_avoids head R x k N w (Nat.find hex) hlt
    apply hv
    rw [← (hw (Nat.find hex)).1]
    exact Nat.find_spec hex
  have ht := historyTrace_stoppedDirectionHistory head x k (boundedWordHit head R x k N) σ
  have hc := historyCursor_stoppedDirectionHistory head x k (boundedWordHit head R x k N) σ
  have hconsume := (instructionTrace_eq_readingState head x k σ t).2
  change rawStackStep head σ R k x = some (historyRoots head x R p, historyCursor head x k p)
  simp only [rawStackStep, dif_pos hex]
  rw [hfind]
  change some (R ∪ {v | v ∈ (loopErase (instructionTrace head (fun v i => σ (v, i)) k x t).2).vertices},
      consume k (instructionTrace head (fun v i => σ (v, i)) k x t).2) =
    some (R ∪ {v | v ∈ (loopErase (historyTrace head x p).2).vertices}, historyCursor head x k p)
  rw [ht, hc, ← hconsume]

end
end FiniteAvalanches.Wilson.Lattice
