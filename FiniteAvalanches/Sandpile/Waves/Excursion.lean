import FiniteAvalanches.Sandpile.Waves.Predecessor

/-! Complete inverse excursions are replayed as actual finite legal avalanches.
The source-three predecessor receives one grain, every intermediate source
height is four, and the final height is the lowest allowed source extension. -/

namespace FiniteAvalanches.Sandpile.Waves

open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

theorem exists_wave_at_height {N : ℕ} {o : FiniteWired.Active N} (h : Punctured N o)
    (s : Site2 → ℤ) (he : ∀ x ∈ boxSites N, s x = wiredHeight 4 h.val x) :
    ∃ v : List Site2, (∀ x ∈ v, x ∈ boxSites N ∧ x ≠ FiniteWired.site o) ∧
      LegalList s (FiniteWired.site o :: v) ∧
      (∀ x ∈ boxSites N, x ≠ FiniteWired.site o →
        0 ≤ heightAfter s (FiniteWired.site o :: v) x ∧ heightAfter s (FiniteWired.site o :: v) x < 4) ∧
      listCounts (FiniteWired.site o :: v) = waveCounts h.val ∧
      ∀ x ∈ boxSites N, heightAfter s (FiniteWired.site o :: v) x =
        wiredHeight (degree (core (forward h).val) (FiniteWired.site o)) (forward h).val x := by
  obtain ⟨v, hv, hl, ht, hc⟩ := wave_counts_realizes h.val
  have hV : ∀ x ∈ FiniteWired.site o :: v, x ∈ boxSites N := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact site_mem_box o
    · exact (hv x hx).1
  refine ⟨v, hv, (legal_list_congr_in he hV).mpr hl, ?_, hc, ?_⟩
  · intro x hx hxo
    simpa only [heightAfter, he x hx] using ht x hx hxo
  · intro x hx
    rw [heightAfter, he x hx, hc]
    by_cases hxo : x = FiniteWired.site o
    · subst x
      rw [wired_height_site, active_height_source, lap_counts_eq_degree (wave_counts_le_one h.val)]
      simp only [source_mem_wave h.val, if_true, mul_one]
      rw [wave_support_eq_core_output h.property, wired_height_site, active_height_source]
      change 4 + ((degree (core (forward h).val) (FiniteWired.site o) : ℤ) - 4) = _
      omega
    · change waveHeight h.val x = wiredHeight _ (waveOutput h.val) x
      rw [← wired_output_height h.val hx hxo, wired_height_off (-1) _ _ hxo]

theorem exists_trace_to_first_terminal {N : ℕ} {o : FiniteWired.Active N}
    (n : ℕ) (h : Punctured N o) (s : Site2 → ℤ)
    (he : ∀ x ∈ boxSites N, s x = wiredHeight 4 h.val x)
    (ht : terminal (forward^[n + 1] h))
    (hi : ∀ k : ℕ, 0 < k → k < n + 1 → ¬terminal (forward^[k] h)) :
    ∃ ws : List (List Site2), ws.length = n + 1 ∧
      IsWaveStabilization (boxSites N) (FiniteWired.site o) s ws ∧
      (∀ x ∈ boxSites N, heightAfter s ws.flatten x =
        wiredHeight (degree (core (forward^[n + 1] h).val) (FiniteWired.site o))
          (forward^[n + 1] h).val x) ∧
      ∀ (k : ℕ) (hk : k < ws.length), listCounts ws[k] = waveCounts (forward^[k] h).val := by
  induction n generalizing h s with
  | zero =>
    obtain ⟨v, hv, hl, hs, hc, hend⟩ := exists_wave_at_height h s he
    have hsrc : 4 ≤ s (FiniteWired.site o) := by rw [he _ (site_mem_box o), wired_height_site, active_height_source]
    have hfin : ∀ x ∈ boxSites N, 0 ≤ heightAfter s (FiniteWired.site o :: v) x ∧
        heightAfter s (FiniteWired.site o :: v) x < 4 := by
      intro x hx
      by_cases hxo : x = FiniteWired.site o
      · subst x
        rw [hend _ (site_mem_box o), wired_height_site, active_height_source]
        have hd := ht
        simp only [zero_add, Function.iterate_one] at hd
        unfold terminal at hd
        exact ⟨Nat.cast_nonneg _, by exact_mod_cast hd⟩
      · exact hs x hx hxo
    refine ⟨[FiniteWired.site o :: v], by simp, IsWaveStabilization.cons (site_mem_box o) hsrc hv hl hs (IsWaveStabilization.nil hfin), ?_, ?_⟩
    · simpa using hend
    · intro k hk
      have hk0 : k = 0 := by simpa using hk
      subst k
      exact hc
  | succ n ih =>
    obtain ⟨v, hv, hl, hs, hc, hend⟩ := exists_wave_at_height h s he
    have hsrc : 4 ≤ s (FiniteWired.site o) := by rw [he _ (site_mem_box o), wired_height_site, active_height_source]
    have hn : ¬terminal (forward h) := by simpa using hi 1 (by omega) (by omega)
    have hnext : ∀ x ∈ boxSites N, heightAfter s (FiniteWired.site o :: v) x = wiredHeight 4 (forward h).val x := by
      intro x hx
      rw [hend x hx]
      have hd := degree_le_four (core (forward h).val) (FiniteWired.site o)
      unfold terminal at hn
      have hd4 : degree (core (forward h).val) (FiniteWired.site o) = 4 := by omega
      simp only [hd4, Nat.cast_ofNat]
    have ht' : terminal (forward^[n + 1] (forward h)) := by simpa only [Function.iterate_succ_apply] using ht
    have hi' : ∀ k : ℕ, 0 < k → k < n + 1 → ¬terminal (forward^[k] (forward h)) := by
      intro k hk hkn
      simpa only [Function.iterate_succ_apply] using hi (k + 1) (by omega) (by omega)
    obtain ⟨ws, hlen, hw, hfinal, hcounts⟩ := ih (forward h) (heightAfter s (FiniteWired.site o :: v)) hnext ht' hi'
    refine ⟨(FiniteWired.site o :: v) :: ws, by simp [hlen], IsWaveStabilization.cons (site_mem_box o) hsrc hv hl hs hw, ?_, ?_⟩
    · intro x hx
      simp only [List.flatten_cons, height_after_append]
      simpa only [Function.iterate_succ_apply] using hfinal x hx
    · intro k hk
      cases k with
      | zero => exact hc
      | succ k =>
        have hk' : k < ws.length := by simpa using hk
        simpa only [List.getElem_cons_succ, Function.iterate_succ_apply] using hcounts k hk'

/-- A whole inverse excursion has the literal source-three legal avalanche,
with exactly the prescribed reversed wave sets and the lowest source extension. -/
theorem exists_excursion_avalanche {N : ℕ} {o : FiniteWired.Active N} (h : TerminalState N o) :
    ∃ ws : List (List Site2), ws.length = returnTime h ∧
      IsWaveStabilization (boxSites N) (FiniteWired.site o)
        (initial (wiredStable (returnMap h).val.val) (FiniteAvalanches.oneGrain (FiniteWired.site o))) ws ∧
      (∀ x ∈ boxSites N, heightAfter (wiredHeight 4 (returnMap h).val.val) ws.flatten x =
        wiredHeight (degree (core h.val.val) (FiniteWired.site o)) h.val.val x) ∧
      ∀ (k : ℕ) (hk : k < ws.length), (listCounts ws[k]).support =
        core (inverse^[returnTime h - (k + 1)] h.val).val := by
  have hr := return_time_pos h
  obtain ⟨ws, hlen, hw, hfin, hc⟩ := exists_trace_to_first_terminal (returnTime h - 1)
    (returnMap h).val (wiredHeight 4 (returnMap h).val.val) (fun _ _ => rfl)
    (by rw [show returnTime h - 1 + 1 = returnTime h by omega, forward_return_map]; exact h.property)
    (fun k hk hkr => not_terminal_inside_forward_excursion h hk (by omega))
  rw [show returnTime h - 1 + 1 = returnTime h by omega] at hlen hfin
  refine ⟨ws, hlen, ?_, ?_, ?_⟩
  · rw [initial_wired_stable]
    exact hw
  · rw [forward_return_map] at hfin
    exact hfin
  · intro k hk
    rw [hc k hk, wave_support_eq_core_output (forward^[k] (returnMap h).val).property]
    change core (forward (forward^[k] (inverse^[returnTime h] h.val))).val = _
    rw [← Function.iterate_succ_apply' forward k]
    rw [forward_inverse_iterate_sub h.val (k + 1) (returnTime h) (by omega)]

/-- The lowest literal recurrent source extension at the excursion's endpoint. -/
def lowestExtension {N : ℕ} {o : FiniteWired.Active N} (h : TerminalState N o) : FiniteWired.Recurrent N :=
  ⟨sourceExtension ⟨degree (core h.val.val) (FiniteWired.site o), h.property⟩ h.val.val,
    (source_extension_recurrent_iff h.val.property _).mpr le_rfl⟩

theorem wired_stable_site {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o)
    (x : FiniteWired.Active N) : wiredStable h (FiniteWired.site x) = sourceExtension 3 h x := by
  have hx : FiniteWired.inBox N (FiniteWired.site x) := fun i => (x i).property
  simp only [wiredStable, dif_pos hx]
  congr 1

theorem excursion_predecessor_height {N : ℕ} {o : FiniteWired.Active N}
    (h : TerminalState N o) (x : FiniteWired.Active N) :
    wiredStable (returnMap h).val.val (FiniteWired.site x) = (excursionPredecessorEquiv h).val.val x := by
  rw [wired_stable_site]
  rfl

/-- Full finite wired stabilization and its actual recurrent endpoint; no
parallel `Stabilizable` object or assumed confinement is used. -/
theorem exists_excursion_wired_stabilization {N : ℕ} {o : FiniteWired.Active N}
    (h : TerminalState N o) : ∃ ws : List (List Site2), ws.length = returnTime h ∧
      WiredStabilizes (wiredStable (returnMap h).val.val) (FiniteAvalanches.oneGrain (FiniteWired.site o))
        (boxSites N) ws.flatten ∧
      (∀ x : FiniteWired.Active N,
        heightAfter (initial (wiredStable (returnMap h).val.val) (FiniteAvalanches.oneGrain (FiniteWired.site o)))
          ws.flatten (FiniteWired.site x) = ((lowestExtension h).val x).val) ∧
      ∀ (k : ℕ) (hk : k < ws.length), (listCounts ws[k]).support =
        core (inverse^[returnTime h - (k + 1)] h.val).val := by
  obtain ⟨ws, hlen, hw, hfin, hsets⟩ := exists_excursion_avalanche h
  refine ⟨ws, hlen, hw.flatten_stable, ?_, hsets⟩
  intro x
  rw [initial_wired_stable, hfin _ (site_mem_box x), wired_height_site]
  exact (source_extension_height ⟨degree (core h.val.val) (FiniteWired.site o), h.property⟩ h.val.val x).symm

end
end FiniteAvalanches.Sandpile.Waves
