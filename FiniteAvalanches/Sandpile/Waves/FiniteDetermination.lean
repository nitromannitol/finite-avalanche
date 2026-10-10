import FiniteAvalanches.Sandpile.Waves.Transfer

/-! The active-site constructor is audited first. Finite determination then
quantifies over every agreeing field and every containing wired volume. -/
namespace FiniteAvalanches.Sandpile.Waves
open LatticeProb LatticeProb.Sandpile FiniteAvalanches FiniteAvalanches.Sandpile
open scoped Classical

/-- An inactive source cannot start a wave. Empty terminal traces remain legal. -/
theorem IsWaveStabilization.eq_nil_of_source_not_mem {V : Finset Site2} {o : Site2}
    {s : Site2 → ℤ} {ws : List (List Site2)}
    (h : IsWaveStabilization V o s ws) (ho : o ∉ V) : ws = [] := by
  cases h with
  | nil => rfl
  | cons hoV => exact (ho hoV).elim

theorem empty_active_trace_iff (o : Site2) (s : Site2 → ℤ)
    (ws : List (List Site2)) : IsWaveStabilization ∅ o s ws ↔ ws = [] := by
  constructor
  · intro h
    exact h.eq_nil_of_source_not_mem (by simp)
  · intro h
    subst ws
    exact .nil (by simp)

/-- The old empty-volume, constant-four, singleton-source trace is rejected. -/
theorem source_outside_counterexample_rejected :
    IsWaveStabilization ∅ (0 : Site2) (fun _ => 4) [] ∧
      ¬IsWaveStabilization ∅ (0 : Site2) (fun _ => 4) [[0]] := by
  simp only [empty_active_trace_iff, List.cons_ne_nil, not_false_eq_true, and_self]

/-- Membership of the source follows from the literal singleton addition support. -/
theorem source_mem_of_affected_subset {o : Site2} {u : Counts} {V : Finset Site2}
    (hV : affected (oneGrain o) u ⊆ V) : o ∈ V := by
  apply hV
  rw [mem_affected_iff]
  exact Or.inl (by simp [oneGrain])

theorem stable_off_source_after_prefix {V : Finset Site2} {o : Site2}
    {s : Site2 → ℤ} {ws : List (List Site2)} (h : IsWaveStabilization V o s ws)
    (hs : ∀ x ∈ V, x ≠ o → 0 ≤ s x ∧ s x < 4) :
    ∀ k : ℕ, k ≤ ws.length → ∀ x ∈ V, x ≠ o →
      0 ≤ heightAfter s (ws.take k).flatten x ∧
        heightAfter s (ws.take k).flatten x < 4 := by
  induction h with
  | nil =>
    intro k hk x hx hxo
    have hk0 : k = 0 := by simpa using hk
    subst k
    simpa only [List.take_zero, List.flatten_nil, height_after_nil] using hs x hx hxo
  | @cons s v ws hoV hsrc hv hl hstable ht ih =>
    intro k hk x hx hxo
    cases k with
    | zero => simpa only [List.take_zero, List.flatten_nil, height_after_nil] using hs x hx hxo
    | succ k =>
      simp only [List.take_succ_cons, List.flatten_cons, height_after_append]
      exact ih hstable k (by simpa using hk) x hx hxo

theorem prefix_affected_subset (ξ : Counts) (ws : List (List Site2)) (k : ℕ) :
    affected ξ (listCounts (ws.take k).flatten) ⊆ affected ξ (listCounts ws.flatten) := by
  apply affected_mono_support
  apply list_counts_support_subset_of_mem
  intro x hx
  obtain ⟨wave, hw, hx⟩ := List.mem_flatten.mp hx
  exact List.mem_flatten.mpr ⟨wave, List.mem_of_mem_take hw, hx⟩

theorem height_after_prefix_outside (η : StableField) (ξ : Counts)
    (ws : List (List Site2)) (k : ℕ) {x : Site2}
    (hx : x ∉ affected ξ (listCounts ws.flatten)) :
    heightAfter (initial η ξ) (ws.take k).flatten x = ((η x).val : ℤ) := by
  have hp : x ∉ affected ξ (listCounts (ws.take k).flatten) :=
    fun h => hx (prefix_affected_subset ξ ws k h)
  simp only [heightAfter, lap_zero_outside_affected hp, add_zero, initial,
    (count_zero_outside_affected hp).1, Nat.cast_zero]

/-- A complete direct formulation of dy:finite-determination, with general finite
additions and the ordered-wave conclusion only for a single grain. Unapproved. -/
theorem finite_determination {η : StableField} {ξ : Counts} {w : List Site2}
    (hw : Stabilizes η ξ w) :
    let K := affected ξ (listCounts w)
    (∀ η' : StableField, (∀ x ∈ K, η' x = η x) →
      (Stabilizes η' ξ w ∧ ∀ v, Stabilizes η' ξ v → listCounts v = listCounts w) ∧
      ∀ V : Finset Site2, K ⊆ V →
        WiredStabilizes η' ξ V w ∧
          ∀ v, WiredStabilizes η' ξ V v → listCounts v = listCounts w) ∧
    (∀ o : Site2, ξ = oneGrain o →
      ∃ ws : List (List Site2), listCounts ws.flatten = listCounts w ∧
        (∀ wave ∈ ws, ∀ x, listCounts wave x ≤ 1) ∧
        ∀ η' : StableField, (∀ x ∈ K, η' x = η x) →
          Stabilizes η' (oneGrain o) ws.flatten ∧
          (∀ k : ℕ, k ≤ ws.length → ∀ x, x ≠ o →
            0 ≤ heightAfter (initial η' (oneGrain o)) (ws.take k).flatten x ∧
              heightAfter (initial η' (oneGrain o)) (ws.take k).flatten x < 4) ∧
          (∀ k : ℕ, k < ws.length →
            heightAfter (initial η' (oneGrain o)) (ws.take k).flatten o = 4) ∧
          ∀ V : Finset Site2, K ⊆ V →
            IsWaveStabilization V o (initial η' (oneGrain o)) ws ∧
            ∀ ws', IsWaveStabilization V o (initial η' (oneGrain o)) ws' →
              ws'.map listCounts = ws.map listCounts ∧
                ws'.map List.toFinset = ws.map List.toFinset ∧ ws'.length = ws.length) := by
  dsimp only
  constructor
  · intro η' heq
    exact finite_determination_counts hw heq
  · intro o hξ
    subst ξ
    obtain ⟨ws, hc, honce, ht⟩ := exists_determined_wave_stabilization hw
    refine ⟨ws, hc, honce, ?_⟩
    intro η' heq
    obtain ⟨hglobal, hK, hV⟩ := ht η' heq
    have hs : ∀ x ∈ affected (oneGrain o) (listCounts w), x ≠ o →
        0 ≤ initial η' (oneGrain o) x ∧ initial η' (oneGrain o) x < 4 := by
      intro x _ hxo
      rw [initial_oneGrain, dirac_of_ne hxo, add_zero]
      exact ⟨Nat.cast_nonneg _, by exact_mod_cast (η' x).isLt⟩
    refine ⟨hglobal, ?_, one_grain_wave_source_heights_eq_four η' o hK, ?_⟩
    · intro k hk x hxo
      by_cases hx : x ∈ affected (oneGrain o) (listCounts w)
      · exact stable_off_source_after_prefix hK hs k hk x hx hxo
      · have hx' : x ∉ affected (oneGrain o) (listCounts ws.flatten) := by simpa only [hc] using hx
        rw [height_after_prefix_outside η' (oneGrain o) ws k hx']
        exact ⟨Nat.cast_nonneg _, by exact_mod_cast (η' x).isLt⟩
    · intro V hKV
      obtain ⟨htrace, huniq⟩ := hV V hKV
      refine ⟨htrace, ?_⟩
      intro ws' hws'
      have hcounts := huniq ws' hws'
      refine ⟨hcounts, ?_, ?_⟩
      · have hsets := congrArg (List.map (fun u : Counts => u.support)) hcounts
        simpa only [List.map_map, Function.comp_def, listCounts_support] using hsets
      · simpa only [List.length_map] using congrArg List.length hcounts

end FiniteAvalanches.Sandpile.Waves
