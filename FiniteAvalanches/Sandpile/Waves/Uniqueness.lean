import FiniteAvalanches.Sandpile.Waves.Stabilization

/-! Independence of the legal order within each successive wave. -/

namespace FiniteAvalanches.Sandpile.Waves

open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open scoped Classical

noncomputable section

theorem legal_list_of_cons {s : Site2 → ℤ} {o : Site2} {v : List Site2}
    (hw : LegalList s (o :: v)) : LegalList (fun x => s x + lap (dirac o) x) v := by
  intro k hk
  have h := hw (k + 1) (by simpa using hk)
  rw [prefix_counts_cons] at h
  simp only [List.getElem_cons_succ, lap_add] at h
  linarith

theorem legal_list_counts_unique_in {s : Site2 → ℤ} {V : Finset Site2} {w v : List Site2}
    (hw : LegalList s w) (hv : LegalList s v)
    (hwV : ∀ x ∈ w, x ∈ V) (hvV : ∀ x ∈ v, x ∈ V)
    (hsw : ∀ x ∈ V, heightAfter s w x < 4)
    (hsv : ∀ x ∈ V, heightAfter s v x < 4) : listCounts w = listCounts v := by
  apply Finsupp.ext
  intro x
  have h1 := wired_legalList_le hw V hwV (listCounts v) hsv w.length x
  have h2 := wired_legalList_le hv V hvV (listCounts w) hsw v.length x
  rw [prefix_eq_terminal w w.length le_rfl] at h1
  rw [prefix_eq_terminal v v.length le_rfl] at h2
  change (listCounts w x : ℤ) ≤ (listCounts v x : ℤ) at h1
  change (listCounts v x : ℤ) ≤ (listCounts w x : ℤ) at h2
  exact_mod_cast le_antisymm h1 h2

theorem wave_counts_unique {s : Site2 → ℤ} {V : Finset Site2} {o : Site2}
    {v v' : List Site2} (hv : ∀ x ∈ v, x ∈ V ∧ x ≠ o)
    (hv' : ∀ x ∈ v', x ∈ V ∧ x ≠ o)
    (hl : LegalList s (o :: v)) (hl' : LegalList s (o :: v'))
    (hs : ∀ x ∈ V, x ≠ o → heightAfter s (o :: v) x < 4)
    (hs' : ∀ x ∈ V, x ≠ o → heightAfter s (o :: v') x < 4) :
    listCounts (o :: v) = listCounts (o :: v') := by
  have hcount := legal_list_counts_unique_in (legal_list_of_cons hl) (legal_list_of_cons hl')
    (V := V.erase o)
    (fun x hx => Finset.mem_erase.mpr ⟨(hv x hx).2, (hv x hx).1⟩)
    (fun x hx => Finset.mem_erase.mpr ⟨(hv' x hx).2, (hv' x hx).1⟩)
    (fun x hx => by
      have h := hs x (Finset.mem_erase.mp hx).2 (Finset.mem_erase.mp hx).1
      simp only [heightAfter, list_counts_cons_int, lap_add] at h ⊢
      linarith)
    (fun x hx => by
      have h := hs' x (Finset.mem_erase.mp hx).2 (Finset.mem_erase.mp hx).1
      simp only [heightAfter, list_counts_cons_int, lap_add] at h ⊢
      linarith)
  apply Finsupp.ext
  intro x
  simp only [listCounts_apply, List.count_cons]
  have hc := congrArg (fun u : Counts => u x) hcount
  simpa only [listCounts_apply] using congrArg (fun n : ℕ => n + if o == x then 1 else 0) hc

theorem IsWaveStabilization.counts_unique {V : Finset Site2} {o : Site2}
    {s : Site2 → ℤ} {ws ws' : List (List Site2)}
    (h : IsWaveStabilization V o s ws) (h' : IsWaveStabilization V o s ws')
    : ws.map listCounts = ws'.map listCounts := by
  induction h generalizing ws' with
  | nil hs =>
    cases h' with
    | nil => rfl
    | cons hoV ho' => have ht := (hs o hoV).2; omega
  | @cons s v ws hoV hsrc hv hl hs ht ih =>
    cases h' with
    | nil hs' => have hlt := (hs' o hoV).2; omega
    | @cons _ v' ws' _ hsrc' hv' hl' hs' ht' =>
      have hc := wave_counts_unique hv hv' hl hl'
        (fun x hx hxo => (hs x hx hxo).2) (fun x hx hxo => (hs' x hx hxo).2)
      have he : heightAfter s (o :: v) = heightAfter s (o :: v') := by
        funext x
        unfold heightAfter
        rw [hc]
      have ht'' : IsWaveStabilization V o (heightAfter s (o :: v)) ws' := by
        rw [he]; exact ht'
      simp only [List.map_cons]
      exact congrArg₂ List.cons hc (ih ht'')

theorem IsWaveStabilization.each_count_le_one {V : Finset Site2} {o : Site2}
    {s : Site2 → ℤ} {ws : List (List Site2)} (h : IsWaveStabilization V o s ws)
    (hs : ∀ x ∈ V, x ≠ o → s x ≤ 3) :
    ∀ w ∈ ws, ∀ x, listCounts w x ≤ 1 := by
  induction h with
  | nil => simp
  | @cons s v ws hoV hsrc hv hl hstable ht ih =>
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · apply count_le_one_of_legal_list o hl
      · intro x hx hxo
        rcases List.mem_cons.mp hx with rfl | hx
        · exact (hxo rfl).elim
        · exact hs x (hv x hx).1 hxo
      · rw [listCounts_apply]
        have hno : o ∉ v := fun h => (hv o h).2 rfl
        simp [List.count_eq_zero_of_not_mem hno]
    · exact ih (fun x hx hxo => by have h := (hstable x hx hxo).2; omega) w hw

theorem IsWaveStabilization.source_heights_eq_four {V : Finset Site2} {o : Site2}
    {s : Site2 → ℤ} {ws : List (List Site2)} (h : IsWaveStabilization V o s ws)
    (hs : ∀ x ∈ V, x ≠ o → s x ≤ 3) (hso : s o ≤ 4) :
    ∀ k : ℕ, k < ws.length → heightAfter s (ws.take k).flatten o = 4 := by
  induction h with
  | nil => simp
  | @cons s v ws hoV hsrc hv hl hstable ht ih =>
    have hno : o ∉ v := fun h => (hv o h).2 rfl
    have hcount : listCounts (o :: v) o = 1 := by
      simp [listCounts_apply, List.count_eq_zero_of_not_mem hno]
    have honce := (IsWaveStabilization.cons hoV hsrc hv hl hstable ht).each_count_le_one hs
      (o :: v) (List.mem_cons_self ..)
    have hnext : heightAfter s (o :: v) o ≤ 4 := by
      simp only [heightAfter, lap, nbrSumZ, Fin.sum_univ_two, hcount]
      have hp0 := honce (o + unit 0)
      have hm0 := honce (o - unit 0)
      have hp1 := honce (o + unit 1)
      have hm1 := honce (o - unit 1)
      norm_num
      omega
    intro k hk
    cases k with
    | zero => simp only [List.take_zero, List.flatten_nil, height_after_nil]; omega
    | succ k =>
      simp only [List.take_succ_cons, List.flatten_cons, height_after_append]
      exact ih (fun x hx hxo => by have h := (hstable x hx hxo).2; omega) hnext k
        (by simpa using hk)

theorem one_grain_wave_source_heights_eq_four (η : StableField) (o : Site2)
    {V : Finset Site2} {ws : List (List Site2)}
    (h : IsWaveStabilization V o (initial η (FiniteAvalanches.oneGrain o)) ws) :
    ∀ k : ℕ, k < ws.length →
      heightAfter (initial η (FiniteAvalanches.oneGrain o)) (ws.take k).flatten o = 4 := by
  apply h.source_heights_eq_four
  · intro x _ hxo
    rw [FiniteAvalanches.initial_oneGrain, dirac_of_ne hxo, add_zero]
    have h := (η x).isLt
    omega
  · exact initial_one_grain_le_four η o o

end
end FiniteAvalanches.Sandpile.Waves
