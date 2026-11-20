import FiniteAvalanches.Wilson.Lattice.HistoryArrows
import FiniteAvalanches.Wilson.Lattice.RowBranchHistory
import FiniteAvalanches.Wilson.Lattice.ErasureAgreement
import FiniteAvalanches.Wilson.Lattice.SamplerTermination

/-! Comparison of recorded direction histories with the lattice Wilson sampler. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb Quiver FiniteAvalanches.Wilson FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- A word trace has the same positions as the lattice walk driven by the word. -/
theorem wordTrace_lattice_position (x : Site 2) (w : WalkDriver) :
    letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
    ∀ n, (wordTrace latticeDirectionHead x w n).1 = position x w n := by
  letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change latticeDirectionHead (wordTrace latticeDirectionHead x w n).1 (w n) =
      position x w n + FiniteWired.step (w n)
    rw [ih]
    rfl

/-- Erasing a lattice word trace agrees with the sampler's list erasure. -/
theorem wordTrace_lattice_loopErase_vertices (x : Site 2) (w : WalkDriver) :
    letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
    ∀ n, (loopErase (wordTrace latticeDirectionHead x w n).2).vertices = walkErase x w n := by
  letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
  intro n
  induction n with
  | zero => simp [wordTrace, loopErase, walkErase, eraseStep]
  | succ n ih =>
    change (loopErase ((wordTrace latticeDirectionHead x w n).2.cons _)).vertices = _
    rw [loopErase_cons_vertices, ih]
    have hwalk : walkErase x w (n + 1) = eraseStep (walkErase x w n) (position x w (n + 1)) := by
      simp only [walkErase, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hwalk]
    congr 1
    exact wordTrace_lattice_position x w (n + 1)

/-- The first hit recorded before a horizon is the sampler's genuine first hit. -/
theorem hitTime_eq_boundedWordHit (R : Set (Site 2)) (x : Site 2)
    (k : Cursor (Site 2)) (N : ℕ) (w : WalkDriver)
    (h : boundedWordHit latticeDirectionHead R x k N w < N) :
    hitTime R x w = some (boundedWordHit latticeDirectionHead R x k N w) := by
  apply (hitTime_eq_some_iff R x w _).mpr
  constructor
  · rw [← wordState_lattice_position x k w]
    exact boundedWordHit_mem_of_lt latticeDirectionHead R x k N w h
  · intro i hi
    rw [← wordState_lattice_position x k w]
    exact boundedWordHit_avoids latticeDirectionHead R x k N w i hi

/-- The erasure in a stopped direction history is the sampler's erased walk. -/
theorem historyTrace_stopped_loopErase_vertices (x : Site 2) (w : WalkDriver) (t : ℕ) :
    letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
    (loopErase (historyTrace latticeDirectionHead x
      (stoppedDirectionHistory (fun _ => t) w)).2).vertices = walkErase x w t := by
  letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
  let p := stoppedDirectionHistory (fun _ => t) w
  have hp : ∀ i < p.1, p.extend i = w i := by
    intro i hi
    have hi' : i < t := hi
    simp only [p, stoppedDirectionHistory, DirectionHistory.extend, dif_pos hi']
  have ht := wordTrace_eq_of_prefix latticeDirectionHead x w p.extend t hp
  change (loopErase (wordTrace latticeDirectionHead x p.extend t).2).vertices = walkErase x w t
  rw [ht]
  exact wordTrace_lattice_loopErase_vertices x w t

/-- An erased finite lattice walk ends at its actual walk endpoint. -/
theorem walkErase_dropLast_append_endpoint (x : Site 2) (w : WalkDriver) (t : ℕ) :
    (walkErase x w t).dropLast ++ [position x w t] = walkErase x w t := by
  letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
  rw [← wordTrace_lattice_position x w t, ← wordTrace_lattice_loopErase_vertices x w t]
  exact Path.dropLast_append_end_eq (loopErase (wordTrace latticeDirectionHead x w t).2)

/-- A recorded first-hit branch produces the same covered set as the sampler. -/
theorem samplerStep_covered_eq_historyRoots (st : SamplerState) (x : Site 2)
    (k : Cursor (Site 2)) (N : ℕ) (w : WalkDriver)
    (h : boundedWordHit latticeDirectionHead st.covered x k N w < N) :
    let t := boundedWordHit latticeDirectionHead st.covered x k N w
    let p := stoppedDirectionHistory (fun _ => t) w
    ∃ out, samplerStep st x w = some out ∧
      out.covered = historyRoots latticeDirectionHead x st.covered p := by
  let t := boundedWordHit latticeDirectionHead st.covered x k N w
  let p := stoppedDirectionHistory (fun _ => t) w
  have ht : hitTime st.covered x w = some t := hitTime_eq_boundedWordHit st.covered x k N w h
  have hroot : position x w t ∈ st.covered := (hitTime_eq_some_iff _ _ _ _).mp ht |>.1
  letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
  have herase := historyTrace_stopped_loopErase_vertices x w t
  change ∃ out, samplerStep st x w = some out ∧
    out.covered = historyRoots latticeDirectionHead x st.covered p
  change (loopErase (historyTrace latticeDirectionHead x p).2).vertices = walkErase x w t at herase
  by_cases hx : x ∈ st.covered
  · have ht0 : hitTime st.covered x w = some 0 := by
      apply (hitTime_eq_some_iff _ _ _ _).mpr
      exact ⟨by simpa only [position_zero] using hx, by simp⟩
    have he : t = 0 := Option.some.inj (ht.symm.trans ht0)
    have hpath : (loopErase (historyTrace latticeDirectionHead x p).2).vertices = [x] := by
      rw [herase, he]
      simp [walkErase, eraseStep]
    refine ⟨st, by simp only [samplerStep, if_pos hx], ?_⟩
    ext v
    simp only [historyRoots, Set.mem_union, Set.mem_setOf_eq, hpath, List.mem_singleton]
    exact ⟨Or.inl, fun h => h.elim id (fun hv => hv.symm ▸ hx)⟩
  · let out : SamplerState :=
      { colors := fun v => if v ∈ (walkErase x w t).dropLast then st.colors (position x w t) else st.colors v
        edges := st.edges ∪ branchEdges (walkErase x w t)
        history := st.history ++ [dirWalkFinite x w t] }
    have hstep : samplerStep st x w = some out := by
      simp only [samplerStep, if_neg hx, ht, out]
    refine ⟨out, hstep, ?_⟩
    ext v
    have hend : st.colors (position x w t) ≠ none := hroot
    have hpath := walkErase_dropLast_append_endpoint x w t
    have hvpath : v ∈ walkErase x w t ↔
        v ∈ (walkErase x w t).dropLast ∨ v = position x w t := by
      conv_lhs => rw [← hpath]
      simp only [List.mem_append, List.mem_singleton]
    change (if v ∈ (walkErase x w t).dropLast then st.colors (position x w t) else st.colors v) ≠ none ↔
      v ∈ st.covered ∪ {v | v ∈ (loopErase (historyTrace latticeDirectionHead x p).2).vertices}
    rw [herase]
    simp only [Set.mem_union, Set.mem_setOf_eq, SamplerState.covered, hvpath]
    by_cases hv : v ∈ (walkErase x w t).dropLast
    · simp only [hv, if_true, or_true, true_or]
      exact ⟨fun _ => trivial, fun _ => hend⟩
    · simp only [hv, if_false, false_or]
      constructor
      · exact Or.inl
      · rintro (hv' | hv')
        · exact hv'
        · simpa only [hv', if_false] using hend

/-- A concatenation of query lists uses the corresponding consecutive rows. -/
theorem samplerRun_append_rows (st : SamplerState) (L M : List (Site 2))
    (rows : ℕ → WalkDriver) :
    samplerRun st (L ++ M) rows = (samplerRun st L rows).bind
      (fun out => samplerRun out M (fun i => rows (i + L.length))) := by
  induction L generalizing st rows with
  | nil => simp only [List.nil_append, samplerRun, Option.bind_some, List.length_nil, Nat.add_zero]
  | cons x xs ih =>
    cases h : samplerStep st x (rows 0) with
    | none => simp only [List.cons_append, samplerRun, h, Option.bind_none]
    | some out =>
      simpa only [List.cons_append, samplerRun, h, Option.bind_some,
        List.length_cons, Nat.add_assoc] using ih out (fun i => rows (i + 1))

/-- A successful row history recovers the sampler's covered set after the
same ordered sequence of lattice queries. -/
theorem samplerRun_covered_eq_rowBranchHistory (st : SamplerState) (x : ℕ → Site 2)
    (k : Cursor (Site 2)) (N n : ℕ) (rows : ℕ → WalkDriver)
    (h : ∀ i < n, (rowBranchHistory latticeDirectionHead x st.covered k N rows (i + 1)).2.1 < N) :
    ∃ out, samplerRun st ((List.range n).map x) rows = some out ∧
      out.covered = branchHistoryRoots latticeDirectionHead x st.covered n
        (rowBranchHistory latticeDirectionHead x st.covered k N rows n) := by
  induction n with
  | zero => exact ⟨st, rfl, rfl⟩
  | succ n ih =>
    have hpast : ∀ i < n,
        (rowBranchHistory latticeDirectionHead x st.covered k N rows (i + 1)).2.1 < N :=
      fun i hi => h i (Nat.lt_succ_of_lt hi)
    obtain ⟨mid, hmid, hroots⟩ := ih hpast
    let a := rowBranchHistory latticeDirectionHead x st.covered k N rows n
    let c := branchHistoryCursor latticeDirectionHead x k n a
    have hhit : boundedWordHit latticeDirectionHead mid.covered (x n) c N (rows n) < N := by
      rw [hroots]
      exact h n (Nat.lt_succ_self n)
    obtain ⟨out, hstep, hout⟩ := samplerStep_covered_eq_historyRoots mid (x n) c N (rows n) hhit
    refine ⟨out, ?_, ?_⟩
    · rw [List.range_succ, List.map_append, samplerRun_append_rows, hmid]
      simp only [Option.bind_some, List.map_singleton, List.length_map, List.length_range,
        samplerRun, Nat.zero_add, hstep]
    · change out.covered = historyRoots latticeDirectionHead (x n)
        (branchHistoryRoots latticeDirectionHead x st.covered n a)
        (stoppedDirectionHistory (boundedWordHit latticeDirectionHead
          (branchHistoryRoots latticeDirectionHead x st.covered n a) (x n) c N) (rows n))
      simp only [stoppedDirectionHistory] at hout ⊢
      rw [hroots] at hout
      exact hout

end
end FiniteAvalanches.Wilson.Lattice
