import FiniteAvalanches.Wilson.Lattice.HistoryColorPropagation
import FiniteAvalanches.Wilson.Lattice.HistorySamplerState

/-! The lattice sampler propagates the colors encoded by stopped branch words. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb Quiver FiniteAvalanches.Wilson FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- The endpoint of a stopped lattice word is its actual walk position. -/
theorem historyTrace_stopped_lattice_endpoint (x : Site 2) (w : WalkDriver) (t : ℕ) :
    (historyTrace latticeDirectionHead x (stoppedDirectionHistory (fun _ => t) w)).1 =
      position x w t := by
  letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
  let p := stoppedDirectionHistory (fun _ => t) w
  have hp : ∀ i < t, p.extend i = w i := by
    intro i hi
    simp only [p, stoppedDirectionHistory, DirectionHistory.extend, dif_pos hi]
  have he := wordTrace_eq_of_prefix latticeDirectionHead x w p.extend t hp
  change (wordTrace latticeDirectionHead x p.extend t).1 = position x w t
  rw [he, wordTrace_lattice_position]

/-- One successful first-hit sampler step propagates precisely the colors
specified by its stopped branch history. -/
theorem samplerStep_colors_eq_history (st out : SamplerState) (x : Site 2)
    (k : Cursor (Site 2)) (N : ℕ) (w : WalkDriver)
    (h : boundedWordHit latticeDirectionHead st.covered x k N w < N)
    (hs : samplerStep st x w = some out) :
    letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
    let t := boundedWordHit latticeDirectionHead st.covered x k N w
    let p := historyTrace latticeDirectionHead x (stoppedDirectionHistory (fun _ => t) w)
    out.colors = fun v => if v ∈ departures (loopErase p.2) then st.colors p.1 else st.colors v := by
  letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
  let t := boundedWordHit latticeDirectionHead st.covered x k N w
  let p := historyTrace latticeDirectionHead x (stoppedDirectionHistory (fun _ => t) w)
  have ht : hitTime st.covered x w = some t := hitTime_eq_boundedWordHit st.covered x k N w h
  have hp : p.1 = position x w t := historyTrace_stopped_lattice_endpoint x w t
  have he : (loopErase p.2).vertices = walkErase x w t :=
    historyTrace_stopped_loopErase_vertices x w t
  have hd : departures (loopErase p.2) = (walkErase x w t).dropLast := by
    change (loopErase p.2).vertices.dropLast = _
    rw [he]
  change out.colors = fun v => if v ∈ departures (loopErase p.2) then st.colors p.1 else st.colors v
  rw [hd, hp]
  by_cases hx : x ∈ st.covered
  · have ht0 : hitTime st.covered x w = some 0 := by
      apply (hitTime_eq_some_iff _ _ _ _).mpr
      exact ⟨by simpa only [position_zero] using hx, by simp⟩
    have heq : t = 0 := Option.some.inj (ht.symm.trans ht0)
    have hout : out = st := by simpa only [samplerStep, if_pos hx, Option.some.injEq] using hs.symm
    subst out
    rw [heq]
    funext v
    simp [walkErase, eraseStep]
  · simp only [samplerStep, if_neg hx, ht, Option.some.injEq] at hs
    subst out
    rfl

/-- The full lattice sampler propagates exactly the colors of its successful
recorded first-hit history. -/
theorem samplerRun_colors_eq_branchHistoryColor (st : SamplerState) (x : ℕ → Site 2)
    (k : Cursor (Site 2)) (N n : ℕ) (rows : ℕ → WalkDriver) (out : SamplerState)
    (h : ∀ i < n, (rowBranchHistory latticeDirectionHead x st.covered k N rows (i + 1)).2.1 < N)
    (hs : samplerRun st ((List.range n).map x) rows = some out) :
    out.colors = branchHistoryColor latticeDirectionHead x st.colors n
      (rowBranchHistory latticeDirectionHead x st.covered k N rows n) := by
  induction n generalizing out with
  | zero =>
    have he : st = out := Option.some.inj hs
    subst out
    rfl
  | succ n ih =>
    have hpast : ∀ i < n,
        (rowBranchHistory latticeDirectionHead x st.covered k N rows (i + 1)).2.1 < N :=
      fun i hi => h i (Nat.lt_succ_of_lt hi)
    obtain ⟨mid, hmid, hroots⟩ := samplerRun_covered_eq_rowBranchHistory st x k N n rows hpast
    have hcolors := ih mid hpast hmid
    let a := rowBranchHistory latticeDirectionHead x st.covered k N rows n
    let c := branchHistoryCursor latticeDirectionHead x k n a
    let t := boundedWordHit latticeDirectionHead mid.covered (x n) c N (rows n)
    have hhit : t < N := by
      change boundedWordHit latticeDirectionHead mid.covered (x n) c N (rows n) < N
      rw [hroots]
      exact h n (Nat.lt_succ_self n)
    have hstep : samplerStep mid (x n) (rows n) = some out := by
      rw [List.range_succ, List.map_append, samplerRun_append_rows, hmid] at hs
      simp only [Option.bind_some, List.map_singleton, List.length_map, List.length_range,
        samplerRun, Nat.zero_add] at hs
      cases he : samplerStep mid (x n) (rows n) with
      | none =>
        simp only [he, Option.bind_none] at hs
        cases hs
      | some s => simpa only [he, Option.bind_some] using hs
    have hcolor := samplerStep_colors_eq_history mid out (x n) c N (rows n) hhit hstep
    letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
    let p := historyTrace latticeDirectionHead (x n) (stoppedDirectionHistory (fun _ => t) (rows n))
    change out.colors = fun v => if v ∈ departures (loopErase p.2) then mid.colors p.1 else mid.colors v at hcolor
    have he : boundedWordHit latticeDirectionHead
        (branchHistoryRoots latticeDirectionHead x st.covered n a) (x n) c N (rows n) = t := by
      rw [← hroots]
    change out.colors = branchHistoryColor latticeDirectionHead x st.colors (n + 1)
      (a, stoppedDirectionHistory (boundedWordHit latticeDirectionHead
        (branchHistoryRoots latticeDirectionHead x st.covered n a) (x n) c N) (rows n))
    simp only [stoppedDirectionHistory]
    rw [he]
    change out.colors = fun v => if v ∈ departures (loopErase p.2) then
      branchHistoryColor latticeDirectionHead x st.colors n a p.1 else
        branchHistoryColor latticeDirectionHead x st.colors n a v
    rw [hcolor, hcolors]

end
end FiniteAvalanches.Wilson.Lattice
