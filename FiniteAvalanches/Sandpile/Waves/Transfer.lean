import FiniteAvalanches.Sandpile.Waves.Uniqueness
import FiniteAvalanches.Sandpile.LocalConfinement

/-! Transfer of literal ordered waves between fields and wired volumes. -/

namespace FiniteAvalanches.Sandpile.Waves

open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile FiniteAvalanches
open scoped Classical

noncomputable section

theorem affected_mono_support {ξ u v : Counts} (h : u.support ⊆ v.support) :
    affected ξ u ⊆ affected ξ v := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (h hx))
  · obtain ⟨y, hy, hx⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨y, h hy, hx⟩)

theorem affected_zero_subset (ξ u : Counts) : affected 0 u ⊆ affected ξ u := by
  intro x hx
  simp only [mem_affected_iff, Finsupp.zero_apply, ne_self_iff_false, false_or] at hx
  rw [mem_affected_iff]
  exact Or.inr hx

theorem list_counts_support_subset_of_mem {w w' : List Site2}
    (h : ∀ x ∈ w, x ∈ w') : (listCounts w).support ⊆ (listCounts w').support := by
  simp only [listCounts_support]
  exact fun x hx => List.mem_toFinset.mpr (h x (List.mem_toFinset.mp hx))

theorem IsWaveStabilization.transfer {V : Finset Site2} {o : Site2}
    {s : Site2 → ℤ} {ws : List (List Site2)} (h : IsWaveStabilization V o s ws) :
    ∀ (s' : Site2 → ℤ) (K V' : Finset Site2),
      affected 0 (listCounts ws.flatten) ⊆ K → K ⊆ V → K ⊆ V' →
      (∀ x ∈ K, s' x = s x) → (∀ x ∉ K, 0 ≤ s' x ∧ s' x < 4) →
      IsWaveStabilization V' o s' ws := by
  induction h with
  | nil hs =>
    intro s' K V' _ hKV _ heq hstable
    apply IsWaveStabilization.nil
    intro x _
    by_cases hx : x ∈ K
    · rw [heq x hx]
      exact hs x (hKV hx)
    · exact hstable x hx
  | @cons s v ws hoV hsrc hv hl hs ht ih =>
    intro s' K V' hK hKV hKV' heq hstable
    have hwSub : (listCounts (o :: v)).support ⊆
        (listCounts (((o :: v) :: ws).flatten)).support :=
      list_counts_support_subset_of_mem (fun x hx => by simp only [List.flatten_cons]; exact List.mem_append_left _ hx)
    have htSub : (listCounts ws.flatten).support ⊆
        (listCounts (((o :: v) :: ws).flatten)).support :=
      list_counts_support_subset_of_mem (fun x hx => by simp only [List.flatten_cons]; exact List.mem_append_right _ hx)
    have hKw := (affected_mono_support (ξ := 0) hwSub).trans hK
    have hKt := (affected_mono_support (ξ := 0) htSub).trans hK
    have hwK : ∀ x ∈ o :: v, x ∈ K := fun x hx => hKw (mem_affected_of_list hx)
    have heqNext : ∀ x ∈ K, heightAfter s' (o :: v) x = heightAfter s (o :: v) x := by
      intro x hx
      simp only [heightAfter, heq x hx]
    have hstableNext : ∀ x ∉ K,
        0 ≤ heightAfter s' (o :: v) x ∧ heightAfter s' (o :: v) x < 4 := by
      intro x hx
      have ha : x ∉ affected 0 (listCounts (o :: v)) := fun h => hx (hKw h)
      simpa only [heightAfter, lap_zero_outside_affected ha, add_zero] using hstable x hx
    have hl' : LegalList s' (o :: v) := by
      intro k hk
      simpa only [heq _ (hwK _ (List.getElem_mem hk))] using hl k hk
    apply IsWaveStabilization.cons
    · exact hKV' (hwK o (List.mem_cons_self ..))
    · rw [heq o (hwK o (List.mem_cons_self ..))]
      exact hsrc
    · intro x hx
      exact ⟨hKV' (hwK x (List.mem_cons_of_mem o hx)), (hv x hx).2⟩
    · exact hl'
    · intro x _ hxo
      by_cases hx : x ∈ K
      · rw [heqNext x hx]
        exact hs x (hKV hx) hxo
      · exact hstableNext x hx
    · exact ih (heightAfter s' (o :: v)) K V' hKt hKV hKV' heqNext hstableNext

/-- Every agreeing stable field and every wired volume containing the affected set
have exactly the same sequence of wave odometers. -/
theorem finite_determination_waves {η η' : StableField} {o : Site2} {R : ℕ}
    {ws : List (List Site2)}
    (h : IsWaveStabilization (boxSites R) o (initial η (oneGrain o)) ws)
    (hK : affected (oneGrain o) (listCounts ws.flatten) ⊆ boxSites R)
    (heq : ∀ x ∈ affected (oneGrain o) (listCounts ws.flatten), η' x = η x)
    (V : Finset Site2) (hV : affected (oneGrain o) (listCounts ws.flatten) ⊆ V) :
    IsWaveStabilization V o (initial η' (oneGrain o)) ws ∧
      ∀ ws', IsWaveStabilization V o (initial η' (oneGrain o)) ws' →
        ws'.map listCounts = ws.map listCounts := by
  have ht := h.transfer (initial η' (oneGrain o))
    (affected (oneGrain o) (listCounts ws.flatten)) V
    (affected_zero_subset (oneGrain o) (listCounts ws.flatten))
    hK hV (fun x hx => by simp only [initial, heq x hx])
    (fun x hx => by
      have hz := (count_zero_outside_affected hx).1
      simp only [initial, hz, Nat.cast_zero, add_zero]
      exact ⟨by positivity, by exact_mod_cast (η' x).isLt⟩)
  exact ⟨ht, fun ws' hws' => hws'.counts_unique ht⟩

/-- Finite legal stabilization determines one common complete ordered wave sequence
for every agreeing field and every volume containing the actual affected set. -/
theorem exists_determined_wave_stabilization {η : StableField} {o : Site2}
    {w : List Site2} (hw : Stabilizes η (oneGrain o) w) :
    ∃ ws : List (List Site2), listCounts ws.flatten = listCounts w ∧
      (∀ wave ∈ ws, ∀ x, listCounts wave x ≤ 1) ∧
      ∀ η' : StableField,
        (∀ x ∈ affected (oneGrain o) (listCounts w), η' x = η x) →
        Stabilizes η' (oneGrain o) ws.flatten ∧
        IsWaveStabilization (affected (oneGrain o) (listCounts w)) o
          (initial η' (oneGrain o)) ws ∧
        ∀ V : Finset Site2, affected (oneGrain o) (listCounts w) ⊆ V →
          IsWaveStabilization V o (initial η' (oneGrain o)) ws ∧
          ∀ ws', IsWaveStabilization V o (initial η' (oneGrain o)) ws' →
            ws'.map listCounts = ws.map listCounts := by
  let K := affected (oneGrain o) (listCounts w)
  let R := K.sup (siteRadius 0)
  have hKR : K ⊆ boxSites R := by
    intro x hx
    apply (site_radius_zero_le_iff x R).mp
    exact Finset.le_sup (f := siteRadius 0) hx
  have hoK : o ∈ K := by
    rw [mem_affected_iff]
    exact Or.inl (by simp [oneGrain])
  obtain ⟨ws, hws, hstab⟩ := exists_wave_stabilization η o R (hKR hoK)
  have hwR : WiredStabilizes η (oneGrain o) (boxSites R) w :=
    ⟨fun x hx => hKR (mem_affected_of_list hx), hw.1, fun x _ => hw.2 x⟩
  have hcount := wiredStabilizes_counts_unique hstab hwR
  have hKws : affected (oneGrain o) (listCounts ws.flatten) ⊆ boxSites R := by
    rw [hcount]
    exact hKR
  have honce := hws.each_count_le_one (fun x _ hxo => by
    rw [initial_oneGrain, dirac_of_ne hxo, add_zero]
    have h := (η x).isLt
    omega)
  refine ⟨ws, hcount, honce, ?_⟩
  intro η' heq
  have heq' : ∀ x ∈ affected (oneGrain o) (listCounts ws.flatten), η' x = η x := by
    simpa only [hcount] using heq
  have htK := (finite_determination_waves hws hKws heq' K (by rw [hcount])).1
  have htFinal := htK.flatten_stable
  have hglobal : Stabilizes η' (oneGrain o) ws.flatten :=
    ⟨htFinal.2.1, by simpa only [hcount] using (stabilizes_transfer hw heq).2⟩
  refine ⟨hglobal, htK, ?_⟩
  intro V hV
  apply finite_determination_waves hws hKws heq' V
  simpa only [hcount] using hV

end
end FiniteAvalanches.Sandpile.Waves
