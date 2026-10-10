import FiniteAvalanches.Sandpile.WiredTermination

/-! Finite legal waves: one source toppling followed by legal off-source topplings. -/

namespace FiniteAvalanches.Sandpile.Waves

open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open scoped Classical

noncomputable section

theorem prefix_counts_le_terminal (w : List Site2) (k : ℕ) (x : Site2) :
    prefixCounts w k x ≤ (listCounts w x : ℤ) := by
  rw [listCounts_apply]
  change ((w.take k).count x : ℤ) ≤ (w.count x : ℤ)
  exact_mod_cast (List.take_sublist k w).count_le x

/-- With at most one source toppling, an off-source vertex cannot topple twice. -/
theorem count_le_one_of_legal_list {s : Site2 → ℤ} {w : List Site2} (o : Site2)
    (hw : LegalList s w) (hs : ∀ x ∈ w, x ≠ o → s x ≤ 3)
    (ho : listCounts w o ≤ 1) : ∀ x, listCounts w x ≤ 1 := by
  have hp : ∀ k x, prefixCounts w k x ≤ 1 := by
    intro k
    induction k with
    | zero => intro x; simp [prefix_zero]
    | succ k ih =>
      intro x
      by_cases hk : k < w.length
      · rw [prefix_succ w k hk x]
        by_cases hx : x = w[k]
        · subst x
          by_cases hxo : w[k] = o
          · have hle := prefix_counts_le_terminal w (k + 1) o
            have hsrc : (listCounts w o : ℤ) ≤ 1 := by exact_mod_cast ho
            have hstep := prefix_succ w k hk o
            rw [hxo] at hstep ⊢
            simp only at hstep ⊢
            omega
          · have ht := hw k hk
            have ht0 := hs w[k] (List.getElem_mem hk) hxo
            have hc := ih w[k]
            have hn : 0 ≤ prefixCounts w k w[k] := Nat.cast_nonneg _
            have hc0 : prefixCounts w k w[k] = 0 := by
              by_contra hne
              have hc1 : prefixCounts w k w[k] = 1 := by omega
              have hl : lap (prefixCounts w k) w[k] ≤ 0 := by
                simp only [lap, nbrSumZ, Fin.sum_univ_two, hc1]
                have h0p := ih (w[k] + unit 0)
                have h0m := ih (w[k] - unit 0)
                have h1p := ih (w[k] + unit 1)
                have h1m := ih (w[k] - unit 1)
                norm_num
                omega
              omega
            simp [hc0]
        · simpa only [if_neg hx, add_zero] using ih x
      · rw [prefix_eq_terminal w (k + 1) (by omega)]
        have hi := ih x
        rw [prefix_eq_terminal w k (by omega)] at hi
        exact hi
  intro x
  have h := hp w.length x
  rw [prefix_eq_terminal w w.length le_rfl] at h
  change (listCounts w x : ℤ) ≤ 1 at h
  exact_mod_cast h

theorem exists_legal_list_stable_in_subset (s : Site2 → ℤ) (R K : ℕ)
    (V : Finset Site2) (hV : V ⊆ boxSites R)
    (hs : ∀ x ∈ V, s x < 4 + 2 * K) :
    ∃ w : List Site2, (∀ x ∈ w, x ∈ V) ∧ LegalList s w ∧
      ∀ x ∈ V, s x + lap (fun y => (listCounts w y : ℤ)) x < 4 := by
  let P (n : ℕ) := ∃ w : List Site2, w.length = n ∧ (∀ x ∈ w, x ∈ V) ∧ LegalList s w
  let B := (boxBarrier R K).sum (fun _ n => n)
  have bound {w : List Site2} (hw : LegalList s w) (hwV : ∀ x ∈ w, x ∈ V) : w.length ≤ B := by
    have hb : ∀ x, listCounts w x ≤ boxBarrier R K x := by
      intro x
      have h := wired_legalList_le hw V hwV (boxBarrier R K)
        (fun y hy => by have hl := lap_box_barrier_le (K := K) (hV hy); linarith [hs y hy])
        w.length x
      rw [prefix_eq_terminal w w.length le_rfl] at h
      change (listCounts w x : ℤ) ≤ (boxBarrier R K x : ℤ) at h
      exact_mod_cast h
    rw [← listCounts_total]
    exact Finsupp.sum_le_sum_index hb (fun _ _ => monotone_id) (fun _ _ => rfl)
  have h0 : P 0 := ⟨[], rfl, by simp, by intro k hk; simp at hk⟩
  obtain ⟨w, hwlen, hwV, hw⟩ := Nat.findGreatest_spec (P := P) (Nat.zero_le B) h0
  refine ⟨w, hwV, hw, ?_⟩
  intro x hx
  by_contra hn
  have hw' := legal_list_append_singleton hw x (by omega)
  have hwV' : ∀ y ∈ w ++ [x], y ∈ V := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hwV y hy
    · simpa using (List.mem_singleton.mp hy) ▸ hx
  have hb := bound hw' hwV'
  have hm := Nat.le_findGreatest (P := P) hb ⟨w ++ [x], rfl, hwV', hw'⟩
  simp only [List.length_append, List.length_singleton] at hm
  omega

theorem prefix_counts_cons (o : Site2) (v : List Site2) (k : ℕ) :
    prefixCounts (o :: v) (k + 1) = fun x => dirac o x + prefixCounts v k x := by
  funext x
  by_cases hx : x = o
  · subst x; simp [prefixCounts, dirac, add_comm]
  · simp [prefixCounts, dirac, hx, Ne.symm hx]

theorem list_counts_cons_int (o : Site2) (v : List Site2) :
    (fun x => (listCounts (o :: v) x : ℤ)) = fun x => dirac o x + (listCounts v x : ℤ) := by
  funext x
  by_cases hx : x = o
  · subst x; simp [listCounts_apply, dirac, add_comm]
  · simp [listCounts_apply, dirac, hx, Ne.symm hx]

theorem legal_list_cons {s : Site2 → ℤ} {o : Site2} {v : List Site2}
    (ho : 4 ≤ s o) (hv : LegalList (fun x => s x + lap (dirac o) x) v) :
    LegalList s (o :: v) := by
  intro k hk
  cases k with
  | zero => simpa [prefix_zero, lap, nbrSumZ] using ho
  | succ k =>
    have hk' : k < v.length := by simpa using hk
    have ht := hv k hk'
    rw [prefix_counts_cons]
    simp only [List.getElem_cons_succ, lap_add]
    linarith

theorem dirac_le_one (o x : Site2) : dirac o x ≤ 1 := by
  unfold dirac
  split <;> norm_num

theorem lap_dirac_le_four (o x : Site2) : lap (dirac o) x ≤ 4 := by
  simp only [lap, nbrSumZ, Fin.sum_univ_two]
  have hp0 := dirac_le_one o (x + unit 0)
  have hm0 := dirac_le_one o (x - unit 0)
  have hp1 := dirac_le_one o (x + unit 1)
  have hm1 := dirac_le_one o (x - unit 1)
  have hn := dirac_nonneg o x
  norm_num
  omega

/-- An unstable source starts a finite legal wave; every vertex topples at most once. -/
theorem exists_legal_wave (s : Site2 → ℤ) (R : ℕ) (V : Finset Site2) (o : Site2)
    (hV : V ⊆ boxSites R) (hoV : o ∈ V) (ho : 4 ≤ s o)
    (hn : ∀ x, 0 ≤ s x) (hs : ∀ x ∈ V, x ≠ o → s x ≤ 3) :
    ∃ v : List Site2, (∀ x ∈ v, x ∈ V ∧ x ≠ o) ∧ LegalList s (o :: v) ∧
      listCounts (o :: v) o = 1 ∧ (∀ x, listCounts (o :: v) x ≤ 1) ∧
      ∀ x ∈ V, x ≠ o →
        0 ≤ s x + lap (fun y => (listCounts (o :: v) y : ℤ)) x ∧
        s x + lap (fun y => (listCounts (o :: v) y : ℤ)) x < 4 := by
  let s' : Site2 → ℤ := fun x => s x + lap (dirac o) x
  obtain ⟨v, hvV, hv, ht⟩ := exists_legal_list_stable_in_subset s' R 2 (V.erase o)
    ((Finset.erase_subset o V).trans hV) (fun x hx => by
      obtain ⟨hxo, hxV⟩ := Finset.mem_erase.mp hx
      have h := hs x hxV hxo
      have hl := lap_dirac_le_four o x
      dsimp [s']
      omega)
  have hvV' : ∀ x ∈ v, x ∈ V ∧ x ≠ o := by
    intro x hx
    have h := Finset.mem_erase.mp (hvV x hx)
    exact ⟨h.2, h.1⟩
  have hw := legal_list_cons ho hv
  have hsrc : listCounts (o :: v) o = 1 := by
    rw [listCounts_apply]
    have hno : o ∉ v := fun h => (hvV' o h).2 rfl
    simp [List.count_eq_zero_of_not_mem hno]
  have honce : ∀ x, listCounts (o :: v) x ≤ 1 :=
    count_le_one_of_legal_list o hw (fun x hx hxo => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (hxo rfl).elim
      · exact hs x (hvV' x hx).1 hxo) (le_of_eq hsrc)
  refine ⟨v, hvV', hw, hsrc, honce, ?_⟩
  intro x hx hxo
  refine ⟨?_, ?_⟩
  · have h := hw.heights_nonneg hn (o :: v).length x
    rw [prefix_eq_terminal _ _ le_rfl] at h
    exact h
  · have h := ht x (Finset.mem_erase.mpr ⟨hxo, hx⟩)
    rw [list_counts_cons_int, lap_add]
    dsimp [s'] at h
    linarith

end
end FiniteAvalanches.Sandpile.Waves
