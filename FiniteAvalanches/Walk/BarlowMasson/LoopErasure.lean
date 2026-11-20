import FiniteAvalanches.Walk.BarlowMasson.Basic
import FiniteAvalanches.Walk.Beurling.Position
import FiniteAvalanches.Wilson.Lattice.Sampler

/-!
# Prefixes of the chronological loop erasure

`walkErase x w T` is the chronological loop erasure of the positions `S_0, …, S_T` of the walk
from `x`. This file records the facts about its prefixes used in the reentry estimate:

* it starts at `x`, ends at `S_T`, has no repeated site, and its consecutive sites are at
  distance at most one;
* (`isPrefix_walkErase_of_avoids`) if `walkErase t = α` and the walk avoids `α` at the times
  `t + 1, …, T`, then `α` is a prefix of `walkErase T`, and the remaining sites are visited at
  those times;
* (`exists_time_of_isPrefix`) conversely, every nonempty prefix `α` of `walkErase T` is
  `walkErase t` for the last time `t ≤ T` at which the walk is at the last site of `α`, and the
  walk avoids `α` after `t`.
-/

noncomputable section

namespace FiniteAvalanches.Walk.BarlowMasson

open LatticeProb MeasureTheory FiniteAvalanches.Walk.Beurling
open FiniteAvalanches.Wilson.Lattice

theorem position_eq (x : Site 2) (w : ℕ → Dir 2) (n : ℕ) : position x w n = walkPos x w n :=
  FiniteAvalanches.Walk.Beurling.position_eq_walkPos x w n

theorem walkErase_zero' (x : Site 2) (w : ℕ → Dir 2) : walkErase x w 0 = [x] := by
  simp [walkErase, eraseStep]

theorem walkErase_succ' (x : Site 2) (w : ℕ → Dir 2) (T : ℕ) :
    walkErase x w (T + 1) = eraseStep (walkErase x w T) (walkPos x w (T + 1)) := by
  simp only [walkErase, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
    position_eq]

theorem eraseStep_eq (l : List (Site 2)) (v : Site 2) :
    eraseStep l v = l.takeWhile (fun u => decide (u ≠ v)) ++ [v] := rfl

theorem takeWhile_ne_append_isPrefix {l : List (Site 2)} {v : Site 2} (hv : v ∈ l) :
    l.takeWhile (fun u => decide (u ≠ v)) ++ [v] <+: l := by
  induction l with
  | nil => simp at hv
  | cons a l ih =>
    by_cases ha : a = v
    · subst ha
      simp
    · have hv' : v ∈ l := (List.mem_cons.1 hv).resolve_left (Ne.symm ha)
      rw [List.takeWhile_cons_of_pos (by simpa using ha), List.cons_append]
      obtain ⟨t, ht⟩ := ih hv'
      exact ⟨t, by rw [List.cons_append, ht]⟩

theorem takeWhile_ne_eq_self {l : List (Site 2)} {v : Site 2} (hv : v ∉ l) :
    l.takeWhile (fun u => decide (u ≠ v)) = l := by
  apply List.takeWhile_eq_self_iff.mpr
  intro u hu
  simpa using fun h : u = v => hv (h ▸ hu)

theorem not_mem_takeWhile_ne (l : List (Site 2)) (v : Site 2) :
    v ∉ l.takeWhile (fun u => decide (u ≠ v)) := by
  intro h
  have := List.mem_takeWhile_imp h
  simp at this

theorem takeWhile_ne_append_of_mem {l m : List (Site 2)} {v : Site 2} (hv : v ∈ l) :
    (l ++ m).takeWhile (fun u => decide (u ≠ v)) = l.takeWhile (fun u => decide (u ≠ v)) := by
  induction l with
  | nil => simp at hv
  | cons a l ih =>
    by_cases ha : a = v
    · subst ha
      simp
    · have hv' : v ∈ l := (List.mem_cons.1 hv).resolve_left (Ne.symm ha)
      simp only [List.cons_append, List.takeWhile_cons, ne_eq, ha,
        not_false_eq_true, decide_true]
      exact congrArg (List.cons a) (ih hv')

theorem walkErase_mem_visited' (x : Site 2) (w : ℕ → Dir 2) (T : ℕ) {v : Site 2}
    (hv : v ∈ walkErase x w T) : ∃ n ≤ T, walkPos x w n = v := by
  induction T generalizing v with
  | zero =>
    rw [walkErase_zero', List.mem_singleton] at hv
    exact ⟨0, le_rfl, by rw [hv, walkPos_zero']⟩
  | succ T ih =>
    rw [walkErase_succ', eraseStep_eq, List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | hv
    · obtain ⟨n, hn, he⟩ := ih (List.takeWhile_subset _ hv)
      exact ⟨n, by omega, he⟩
    · exact ⟨T + 1, le_rfl, hv.symm⟩

theorem walkErase_ne_nil (x : Site 2) (w : ℕ → Dir 2) (T : ℕ) : walkErase x w T ≠ [] := by
  cases T with
  | zero => simp [walkErase_zero']
  | succ T => simp [walkErase_succ', eraseStep_eq]

theorem walkErase_getLast (x : Site 2) (w : ℕ → Dir 2) (T : ℕ) :
    (walkErase x w T).getLast (walkErase_ne_nil x w T) = walkPos x w T := by
  cases T with
  | zero => simp [walkErase_zero', walkPos_zero']
  | succ T => simp [walkErase_succ', eraseStep_eq]

theorem walkErase_start (x : Site 2) (w : ℕ → Dir 2) (T : ℕ) :
    ∃ l, walkErase x w T = x :: l := by
  induction T with
  | zero => exact ⟨[], walkErase_zero' x w⟩
  | succ T ih =>
    obtain ⟨l, hl⟩ := ih
    rw [walkErase_succ', eraseStep_eq, hl]
    by_cases hx : x = walkPos x w (T + 1)
    · refine ⟨[], ?_⟩
      rw [List.takeWhile_cons_of_neg (by simpa using hx), List.nil_append, ← hx]
    · refine ⟨l.takeWhile (fun u => decide (u ≠ walkPos x w (T + 1))) ++
        [walkPos x w (T + 1)], ?_⟩
      rw [List.takeWhile_cons_of_pos (by simpa using hx)]
      simp

theorem walkErase_nodup (x : Site 2) (w : ℕ → Dir 2) (T : ℕ) : (walkErase x w T).Nodup := by
  induction T with
  | zero => simp [walkErase_zero']
  | succ T ih =>
    rw [walkErase_succ', eraseStep_eq, List.nodup_append]
    refine ⟨(List.takeWhile_sublist _).nodup ih, List.nodup_singleton _, ?_⟩
    intro a ha b hb hab
    rw [List.mem_singleton] at hb
    subst hb
    subst hab
    exact not_mem_takeWhile_ne _ _ ha

theorem walkErase_chain (x : Site 2) (w : ℕ → Dir 2) (T : ℕ) :
    (walkErase x w T).IsChain (fun a b => euclidNorm (b - a) ≤ 1) := by
  induction T with
  | zero => rw [walkErase_zero']; exact List.isChain_singleton _
  | succ T ih =>
    rw [walkErase_succ', eraseStep_eq]
    by_cases hv : walkPos x w (T + 1) ∈ walkErase x w T
    · exact ih.infix (takeWhile_ne_append_isPrefix hv).isInfix
    · rw [takeWhile_ne_eq_self hv]
      refine ih.append (List.isChain_singleton _) fun a ha b hb => ?_
      rw [List.head?_cons, Option.mem_some_iff] at hb
      subst hb
      rw [List.getLast?_eq_some_getLast (walkErase_ne_nil x w T), Option.mem_some_iff] at ha
      rw [← ha, walkErase_getLast]
      have h : walkPos x w (T + 1) = walkPos x w T + dirVec (w T) := by
        simp [walkPos, Finset.sum_range_succ, add_assoc]
      rw [h, add_sub_cancel_left, euclidNorm_dirVec]

/-- **Persistence of a prefix.** If the erasure at time `t` is `α` and the walk avoids `α` at the
times `t + 1, …, T`, then `α` is a prefix of the erasure at time `T`, and every site after the
prefix is visited at a time in `(t, T]`. -/
theorem isPrefix_walkErase_of_avoids (x : Site 2) (w : ℕ → Dir 2) {t T : ℕ} (htT : t ≤ T)
    (havoid : ∀ s, t < s → s ≤ T → walkPos x w s ∉ walkErase x w t) :
    ∃ q, walkErase x w T = walkErase x w t ++ q ∧
      ∀ v ∈ q, ∃ s, t < s ∧ s ≤ T ∧ walkPos x w s = v := by
  induction T, htT using Nat.le_induction with
  | base => exact ⟨[], by simp, by simp⟩
  | succ n hn ih =>
    obtain ⟨q, hq, hqv⟩ := ih fun s hs1 hs2 => havoid s hs1 (by omega)
    have hv := havoid (n + 1) (by omega) le_rfl
    refine ⟨q.takeWhile (fun u => decide (u ≠ walkPos x w (n + 1))) ++ [walkPos x w (n + 1)],
      ?_, ?_⟩
    · rw [walkErase_succ', eraseStep_eq, hq, List.takeWhile_append_of_pos, List.append_assoc]
      intro u hu
      simpa using fun h : u = walkPos x w (n + 1) => hv (h ▸ hu)
    · intro v hv'
      rw [List.mem_append, List.mem_singleton] at hv'
      rcases hv' with hv' | hv'
      · obtain ⟨s, hs1, hs2, hs3⟩ := hqv v (List.takeWhile_subset _ hv')
        exact ⟨s, hs1, by omega, hs3⟩
      · exact ⟨n + 1, by omega, le_rfl, hv'.symm⟩

/-- A site that is not in the erasure stays out of it while the walk does not visit it. -/
theorem not_mem_walkErase_of_not_visited (x : Site 2) (w : ℕ → Dir 2) {z : Site 2} {n m : ℕ}
    (hnm : n ≤ m) (hz : z ∉ walkErase x w n) (hvis : ∀ s, n < s → s ≤ m → walkPos x w s ≠ z) :
    z ∉ walkErase x w m := by
  induction m, hnm using Nat.le_induction with
  | base => exact hz
  | succ m hm ih =>
    rw [walkErase_succ', eraseStep_eq, List.mem_append, List.mem_singleton]
    rintro (h | h)
    · exact ih (fun s h1 h2 => hvis s h1 (by omega)) (List.takeWhile_subset _ h)
    · exact hvis (m + 1) (by omega) le_rfl h.symm

private theorem prefix_or_not_mem (x : Site 2) (w : ℕ → Dir 2) {t : ℕ} {z : Site 2}
    (hz : walkPos x w t = z) {n : ℕ} (htn : t ≤ n)
    (hvis : ∀ s, t < s → s ≤ n → walkPos x w s ≠ z) :
    walkErase x w t <+: walkErase x w n ∨ z ∉ walkErase x w n := by
  induction n, htn using Nat.le_induction with
  | base => exact Or.inl (List.prefix_refl _)
  | succ n hn ih =>
    have hvn : walkPos x w (n + 1) ≠ z := hvis (n + 1) (by omega) le_rfl
    rcases ih (fun s h1 h2 => hvis s h1 (by omega)) with ⟨q, hq⟩ | hnot
    · by_cases hvL : walkPos x w (n + 1) ∈ walkErase x w t
      · right
        rw [walkErase_succ', eraseStep_eq, ← hq, takeWhile_ne_append_of_mem hvL,
          List.mem_append, List.mem_singleton]
        rintro (h | h)
        · -- the truncation stops before `z`, the last site of the erasure at time `t`
          have hlast := walkErase_getLast x w t
          rw [hz] at hlast
          have hnd := walkErase_nodup x w t
          obtain ⟨front, hfront⟩ : ∃ front, walkErase x w t = front ++ [z] := by
            refine ⟨(walkErase x w t).dropLast, ?_⟩
            conv_lhs => rw [← List.dropLast_append_getLast (walkErase_ne_nil x w t)]
            rw [hlast]
          rw [hfront] at hvL h hnd
          have hvfront : walkPos x w (n + 1) ∈ front := by
            rcases List.mem_append.1 hvL with h' | h'
            · exact h'
            · exact absurd (List.mem_singleton.1 h') hvn
          rw [takeWhile_ne_append_of_mem hvfront] at h
          have hzf : z ∈ front := List.takeWhile_subset _ h
          exact (List.nodup_append.1 hnd).2.2 _ hzf _ (List.mem_singleton_self _) rfl
        · exact hvn h.symm
      · left
        refine ⟨q.takeWhile (fun u => decide (u ≠ walkPos x w (n + 1))) ++
          [walkPos x w (n + 1)], ?_⟩
        rw [walkErase_succ', eraseStep_eq, ← hq, List.takeWhile_append_of_pos, List.append_assoc]
        intro u hu
        simpa using fun h : u = walkPos x w (n + 1) => hvL (h ▸ hu)
    · right
      exact not_mem_walkErase_of_not_visited x w (Nat.le_succ n) hnot
        (fun s h1 h2 => by rw [show s = n + 1 by omega]; exact hvn)

/-- Two nonempty prefixes of a list without repetitions with the same last element are equal. -/
theorem prefix_eq_of_getLast_eq {l a b : List (Site 2)} (hl : l.Nodup) (ha : a <+: l)
    (hb : b <+: l) (ha0 : a ≠ []) (hb0 : b ≠ []) (hlast : a.getLast ha0 = b.getLast hb0) :
    a = b := by
  have key : ∀ {a b : List (Site 2)} (ha0 : a ≠ []) (hb0 : b ≠ []), b.Nodup → a <+: b →
      a.getLast ha0 = b.getLast hb0 → a = b := by
    intro a b ha0 hb0 hnd hab hlast
    obtain ⟨c, rfl⟩ := hab
    by_cases hc : c = []
    · simp [hc]
    · exfalso
      rw [List.getLast_append_of_ne_nil (by simp [hc]) hc] at hlast
      exact (List.nodup_append.1 hnd).2.2 _ (List.getLast_mem ha0) _ (List.getLast_mem hc) hlast
  rcases le_total a.length b.length with h | h
  · exact key ha0 hb0 (hb.sublist.nodup hl) (List.prefix_of_prefix_length_le ha hb h) hlast
  · exact (key hb0 ha0 (ha.sublist.nodup hl) (List.prefix_of_prefix_length_le hb ha h)
      hlast.symm).symm

/-- **The last visit.** A nonempty prefix `α` of the erasure at time `T` is the erasure at some
time `t ≤ T`, after which the walk avoids `α` up to `T`. -/
theorem exists_time_of_isPrefix (x : Site 2) (w : ℕ → Dir 2) {T : ℕ} {α : List (Site 2)}
    (hα : α ≠ []) (hpre : α <+: walkErase x w T) :
    ∃ t ≤ T, walkErase x w t = α ∧ ∀ s, t < s → s ≤ T → walkPos x w s ∉ α := by
  classical
  set z := α.getLast hα with hzdef
  have hzT : z ∈ walkErase x w T := hpre.subset (List.getLast_mem hα)
  obtain ⟨n₀, hn₀, hvis₀⟩ := walkErase_mem_visited' x w T hzT
  have hex : ∃ t, t ≤ T ∧ walkPos x w t = z ∧ ∀ s, t < s → s ≤ T → walkPos x w s ≠ z := by
    let P := fun t => t ≤ T ∧ walkPos x w t = z
    obtain ⟨t, ht, hmax⟩ : ∃ t, P t ∧ ∀ s, P s → s ≤ t :=
      ⟨Nat.findGreatest P T, Nat.findGreatest_spec (P := P) hn₀ ⟨hn₀, hvis₀⟩,
        fun s hs => Nat.le_findGreatest hs.1 hs⟩
    exact ⟨t, ht.1, ht.2, fun s h1 h2 h3 => absurd (hmax s ⟨h2, h3⟩) (by omega)⟩
  obtain ⟨t, htT, hzt, hvis⟩ := hex
  have hstay : ∀ n, t ≤ n → n ≤ T → walkErase x w t <+: walkErase x w n := by
    intro n htn hnT
    refine (prefix_or_not_mem x w hzt htn fun s h1 h2 => hvis s h1 (by omega)).resolve_right ?_
    intro hz
    exact not_mem_walkErase_of_not_visited x w hnT hz (fun s h1 h2 => hvis s (by omega) h2) hzT
  have hlast_t : (walkErase x w t).getLast (walkErase_ne_nil x w t) = z := by
    rw [walkErase_getLast, hzt]
  have heq : walkErase x w t = α :=
    prefix_eq_of_getLast_eq (walkErase_nodup x w T) (hstay T htT le_rfl) hpre
      (walkErase_ne_nil x w t) hα hlast_t
  refine ⟨t, htT, heq, fun s hs1 hs2 hmem => ?_⟩
  obtain ⟨q, hq⟩ := hstay s hs1.le hs2
  have hnd := walkErase_nodup x w s
  have hls := walkErase_getLast x w s
  rw [← hq] at hnd
  have hsz : walkPos x w s ≠ z := hvis s hs1 hs2
  rw [heq] at hq hnd
  by_cases hqe : q = []
  · subst hqe
    simp only [List.append_nil] at hq
    have : (walkErase x w s).getLast (walkErase_ne_nil x w s) = α.getLast hα := by
      simp only [hq]
    rw [hls] at this
    exact hsz this
  · have h1 : (α ++ q).getLast (by simp [hα]) = walkPos x w s := by
      rw [← hls]
      simp only [hq]
    rw [List.getLast_append_of_ne_nil (by simp [hqe]) hqe] at h1
    exact (List.nodup_append.1 hnd).2.2 _ hmem _ (List.getLast_mem hqe) h1.symm

end FiniteAvalanches.Walk.BarlowMasson
