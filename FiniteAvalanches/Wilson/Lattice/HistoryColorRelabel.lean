import FiniteAvalanches.Wilson.Lattice.HistoryColorPropagation

/-! Color propagation along compatibly relabeled branch histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open Quiver FiniteAvalanches.Wilson FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- Every branch has the same endpoint and loop-erased vertices under a
vertex embedding, with endpoints in the selected domain. -/
def BranchHistory.ColorCompatible (head : V → FiniteWired.Direction → V)
    (head' : W → FiniteWired.Direction → W) (x : ℕ → V) (y : ℕ → W)
    (f : V → W) (T : Set V) : (n : ℕ) → BranchHistory n → Prop
  | 0, _ => True
  | n + 1, h => by
    letI : Quiver V := instructionQuiver head
    letI : Quiver W := instructionQuiver head'
    let p := historyTrace head (x n) h.2
    let q := historyTrace head' (y n) h.2
    exact BranchHistory.ColorCompatible head head' x y f T n h.1 ∧
      p.1 ∈ T ∧ f p.1 = q.1 ∧ (loopErase p.2).vertices.map f = (loopErase q.2).vertices

/-- Compatible histories propagate the same colors at all vertices in the
specified domain. -/
theorem branchHistoryColor_map_eq (head : V → FiniteWired.Direction → V)
    (head' : W → FiniteWired.Direction → W) (x : ℕ → V) (y : ℕ → W)
    (f : V → W) (hf : Function.Injective f) (T : Set V)
    (seed : V → Option Bool) (seed' : W → Option Bool)
    (hseed : ∀ v ∈ T, seed v = seed' (f v)) (n : ℕ) (h : BranchHistory n)
    (hc : BranchHistory.ColorCompatible head head' x y f T n h) :
    ∀ v ∈ T, branchHistoryColor head x seed n h v = branchHistoryColor head' y seed' n h (f v) := by
  letI : Quiver V := instructionQuiver head
  letI : Quiver W := instructionQuiver head'
  induction n with
  | zero => exact hseed
  | succ n ih =>
    let p := historyTrace head (x n) h.2
    let q := historyTrace head' (y n) h.2
    have hp : p.1 ∈ T := hc.2.1
    have he : f p.1 = q.1 := hc.2.2.1
    have hvtx : (loopErase p.2).vertices.map f = (loopErase q.2).vertices := hc.2.2.2
    have hdeps : (departures (loopErase p.2)).map f = departures (loopErase q.2) := by
      change (loopErase p.2).vertices.dropLast.map f = (loopErase q.2).vertices.dropLast
      rw [List.map_dropLast, hvtx]
    intro v hv
    have hm : v ∈ departures (loopErase p.2) ↔ f v ∈ departures (loopErase q.2) := by
      rw [← hdeps, List.mem_map]
      constructor
      · intro hvp
        exact ⟨v, hvp, rfl⟩
      · rintro ⟨u, hu, huf⟩
        exact (hf huf) ▸ hu
    change (if v ∈ departures (loopErase p.2) then branchHistoryColor head x seed n h.1 p.1
      else branchHistoryColor head x seed n h.1 v) =
      (if f v ∈ departures (loopErase q.2) then branchHistoryColor head' y seed' n h.1 q.1
      else branchHistoryColor head' y seed' n h.1 (f v))
    by_cases hmem : v ∈ departures (loopErase p.2)
    · rw [if_pos hmem, if_pos (hm.mp hmem), ← he]
      exact ih h.1 hc.1 p.1 hp
    · rw [if_neg hmem, if_neg (hm.not.mp hmem)]
      exact ih h.1 hc.1 v hv

end
end FiniteAvalanches.Wilson.Lattice
