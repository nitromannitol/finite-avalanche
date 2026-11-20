import FiniteAvalanches.Wilson.Lattice.RowSamplerBridge

/-! Reconstructing the full lattice sampler state from stopped branch words. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Run the lattice sampler on the finite direction words in a branch history. -/
def branchHistorySampler (x : ℕ → Site 2) (st : SamplerState) :
    (n : ℕ) → BranchHistory n → Option SamplerState
  | 0, _ => some st
  | n + 1, h => (branchHistorySampler x st n h.1).bind fun out =>
      samplerStep out (x n) h.2.extend

/-- Finite direction words determine the full sampler state, including colors,
original edges and the actual finite walk history. -/
theorem samplerRun_eq_branchHistorySampler (st : SamplerState) (x : ℕ → Site 2)
    (k : Cursor (Site 2)) (N n : ℕ) (rows : ℕ → WalkDriver)
    (h : ∀ i < n, (rowBranchHistory latticeDirectionHead x st.covered k N rows (i + 1)).2.1 < N) :
    samplerRun st ((List.range n).map x) rows =
      branchHistorySampler x st n (rowBranchHistory latticeDirectionHead x st.covered k N rows n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpast : ∀ i < n,
        (rowBranchHistory latticeDirectionHead x st.covered k N rows (i + 1)).2.1 < N :=
      fun i hi => h i (Nat.lt_succ_of_lt hi)
    obtain ⟨mid, hmid, hroots⟩ := samplerRun_covered_eq_rowBranchHistory st x k N n rows hpast
    have hrec := ih hpast
    rw [hmid] at hrec
    let a := rowBranchHistory latticeDirectionHead x st.covered k N rows n
    let c := branchHistoryCursor latticeDirectionHead x k n a
    let t := boundedWordHit latticeDirectionHead mid.covered (x n) c N (rows n)
    let p := stoppedDirectionHistory (fun _ => t) (rows n)
    have hhit : t < N := by
      change boundedWordHit latticeDirectionHead mid.covered (x n) c N (rows n) < N
      rw [hroots]
      exact h n (Nat.lt_succ_self n)
    have ht : hitTime mid.covered (x n) (rows n) = some t :=
      hitTime_eq_boundedWordHit mid.covered (x n) c N (rows n) hhit
    have hp : ∀ i < t, p.extend i = rows n i := by
      intro i hi
      simp only [p, stoppedDirectionHistory, DirectionHistory.extend, dif_pos hi]
    have hpos : ∀ i ≤ t, position (x n) p.extend i = position (x n) (rows n) i := by
      intro i hi
      rw [← wordState_lattice_position (x n) c p.extend,
        ← wordState_lattice_position (x n) c (rows n)]
      exact congrArg Prod.fst (wordState_eq_of_prefix latticeDirectionHead (x n) c (rows n)
        p.extend i (fun j hj => hp j (lt_of_lt_of_le hj hi)))
    have hstep := samplerStep_eq_of_positions mid (x n) (rows n) p.extend t ht hpos
    rw [List.range_succ, List.map_append, samplerRun_append_rows, hmid]
    simp only [Option.bind_some, List.map_singleton, List.length_map, List.length_range]
    change samplerRun mid [x n] (fun i => rows (i + n)) =
      (branchHistorySampler x st n a).bind fun out => samplerStep out (x n)
        (stoppedDirectionHistory (boundedWordHit latticeDirectionHead
          (branchHistoryRoots latticeDirectionHead x st.covered n a) (x n) c N) (rows n)).extend
    rw [← hrec]
    simp only [Option.bind_some, samplerRun, Nat.zero_add]
    have he : boundedWordHit latticeDirectionHead
        (branchHistoryRoots latticeDirectionHead x st.covered n a) (x n) c N (rows n) = t := by
      rw [← hroots]
    have hb : (samplerStep mid (x n) (rows n)).bind (fun a => some a) =
        samplerStep mid (x n) (rows n) := by
      cases samplerStep mid (x n) (rows n) <;> rfl
    rw [hb]
    change samplerStep mid (x n) (rows n) =
      samplerStep mid (x n) (stoppedDirectionHistory (boundedWordHit latticeDirectionHead
        (branchHistoryRoots latticeDirectionHead x st.covered n a) (x n) c N) (rows n)).extend
    simp only [stoppedDirectionHistory]
    rw [he]
    exact hstep.symm

end
end FiniteAvalanches.Wilson.Lattice
