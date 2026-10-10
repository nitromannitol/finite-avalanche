import FiniteAvalanches.Sandpile.Waves.SourceExtension

/-! Actual finite wave termination forces every forward orbit to reach a state
with a missing source neighbor. No wave-termination or orbit-hitting premise is added. -/

namespace FiniteAvalanches.Sandpile.Waves

open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

def terminal {N : ℕ} {o : FiniteWired.Active N} (h : Punctured N o) : Prop :=
  degree (core h.val) (FiniteWired.site o) < 4

theorem degree_le_four (A : Finset Site2) (x : Site2) : degree A x ≤ 4 := by
  have hi : ∀ y : Site2, (if y ∈ A then (1 : ℤ) else 0) ≤ 1 := by
    intro y
    split <;> norm_num
  have he := degree_eq_sum A x
  simp only [nbrSumZ, Fin.sum_univ_two] at he
  have hp0 := hi (x + unit 0)
  have hm0 := hi (x - unit 0)
  have hp1 := hi (x + unit 1)
  have hm1 := hi (x - unit 1)
  omega

theorem legal_list_congr_in {V : Finset Site2} {s t : Site2 → ℤ} {w : List Site2}
    (he : ∀ x ∈ V, s x = t x) (hV : ∀ x ∈ w, x ∈ V) :
    LegalList s w ↔ LegalList t w := by
  constructor <;> intro hw k hk
  · rw [← he w[k] (hV w[k] (List.getElem_mem hk))]
    exact hw k hk
  · rw [he w[k] (hV w[k] (List.getElem_mem hk))]
    exact hw k hk

theorem trace_reaches_terminal {N : ℕ} {o : FiniteWired.Active N} {s : Site2 → ℤ}
    {ws : List (List Site2)} (ht : IsWaveStabilization (boxSites N) (FiniteWired.site o) s ws)
    (h : Punctured N o) (he : ∀ x ∈ boxSites N, s x = wiredHeight 4 h.val x) :
    ∃ n : ℕ, 0 < n ∧ terminal (forward^[n] h) := by
  induction ht generalizing h with
  | nil hs =>
    have hh := (hs (FiniteWired.site o) (site_mem_box o)).2
    rw [he _ (site_mem_box o), wired_height_site, active_height_source] at hh
    omega
  | @cons s v ws hoV hsrc hv hl hs ht ih =>
    have hV : ∀ x ∈ FiniteWired.site o :: v, x ∈ boxSites N := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact site_mem_box o
      · exact (hv x hx).1
    have hl' := (legal_list_congr_in he hV).mp hl
    have ht' : ∀ x ∈ boxSites N, x ≠ FiniteWired.site o →
        0 ≤ heightAfter (wiredHeight 4 h.val) (FiniteWired.site o :: v) x ∧
        heightAfter (wiredHeight 4 h.val) (FiniteWired.site o :: v) x < 4 := by
      intro x hx hxo
      simpa only [heightAfter, he x hx] using hs x hx hxo
    have hc := wave_counts_eq (h := h.val) ⟨v, hv, hl', ht', rfl⟩
    have hsource : heightAfter s (FiniteWired.site o :: v) (FiniteWired.site o) =
        (degree (core (forward h).val) (FiniteWired.site o) : ℤ) := by
      rw [heightAfter, he _ (site_mem_box o), wired_height_site, active_height_source, hc,
        lap_counts_eq_degree (wave_counts_le_one h.val)]
      simp only [source_mem_wave h.val, if_true, mul_one]
      rw [wave_support_eq_core_output h.property]
      change 4 + ((degree (core (forward h).val) (FiniteWired.site o) : ℤ) - 4) = _
      omega
    by_cases hterm : terminal (forward h)
    · exact ⟨1, by omega, by simpa only [Function.iterate_one] using hterm⟩
    · have he' : ∀ x ∈ boxSites N,
          heightAfter s (FiniteWired.site o :: v) x = wiredHeight 4 (forward h).val x := by
        intro x hx
        by_cases hxo : x = FiniteWired.site o
        · subst x
          rw [hsource, wired_height_site, active_height_source]
          have hd := degree_le_four (core (forward h).val) (FiniteWired.site o)
          unfold terminal at hterm
          omega
        · rw [heightAfter, he x hx, hc]
          change waveHeight h.val x = wiredHeight 4 (waveOutput h.val) x
          rw [← wired_output_height h.val hx hxo, wired_height_off (-1) 4 _ hxo]
      obtain ⟨n, hn, ht'⟩ := ih (forward h) he'
      exact ⟨n + 1, by omega, by simpa only [Function.iterate_succ_apply] using ht'⟩

/-- Auxiliary stable extension to the wired exterior, which is a sink. -/
def wiredStable {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o) : StableField :=
  fun x => if hx : FiniteWired.inBox N x then sourceExtension 3 h (FiniteWired.activeOfSite N x hx) else 0

theorem initial_wired_stable {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o) :
    initial (wiredStable h) (FiniteAvalanches.oneGrain (FiniteWired.site o)) = wiredHeight 4 h := by
  funext x
  rw [FiniteAvalanches.initial_oneGrain]
  have he : ((wiredStable h x).val : ℤ) = wiredHeight 3 h x := by
    unfold wiredStable wiredHeight
    split
    · rw [source_extension_height]
      rfl
    · rfl
  rw [he]
  by_cases hxo : x = FiniteWired.site o
  · subst x
    rw [wired_height_site, wired_height_site, active_height_source, active_height_source]
    simp [dirac]
  · rw [dirac_of_ne hxo, add_zero, wired_height_off 3 4 h hxo]

/-- Every orbit hits the actual source-extension locus, by finite legal termination. -/
theorem forward_orbit_reaches_terminal {N : ℕ} {o : FiniteWired.Active N} (h : Punctured N o) :
    ∃ n : ℕ, 0 < n ∧ terminal (forward^[n] h) := by
  obtain ⟨ws, hws, _⟩ := exists_wave_stabilization (wiredStable h.val) (FiniteWired.site o) N (site_mem_box o)
  rw [initial_wired_stable] at hws
  exact trace_reaches_terminal hws h (fun _ _ => rfl)

end
end FiniteAvalanches.Sandpile.Waves
