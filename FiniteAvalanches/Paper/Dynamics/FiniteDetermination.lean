import FiniteAvalanches.Sandpile.Waves.FiniteDetermination

set_option autoImplicit false
namespace FiniteAvalanches.Paper.Dynamics
open LatticeProb LatticeProb.Sandpile FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves
open scoped Classical
noncomputable section

/-- Finite determination of additions. Let `η` be stable and `ξ` a finitely supported
addition such that `η + ξ` has a finite legal stabilization, with odometer `u`, and put
`K = supp ξ ∪ supp u ∪ N(supp u)`. Every stable field `η'` agreeing with `η` on `K` has a
finite legal stabilization with the same odometer; so does its restriction to every wired
volume `V ⊇ K`. If `ξ` is a single grain at `o`, the ordered list of wave supports is also
the same: for every such `η'`, both for the waves in `ℤ²` (a trace that is a wave
stabilization on some finite volume containing everything it affects) and for the waves in
every wired volume `V ⊇ K`. -/
theorem finite_determination (η : StableField) (ξ : Counts)
    (hη : ∃ w : List Site2, Stabilizes η ξ w) :
    let u : Counts := odometer ξ ⟨η, hη⟩
    let K : Finset Site2 := affected ξ u
    (∀ η' : StableField, (∀ x ∈ K, η' x = η x) →
      (∃ ζ : StabilizationDomain ξ, ζ.val = η' ∧ odometer ξ ζ = u) ∧
      ∀ V : Finset Site2, K ⊆ V →
        (∃ w : List Site2, WiredStabilizes η' ξ V w) ∧
        ∀ w : List Site2, WiredStabilizes η' ξ V w → listCounts w = u) ∧
    (∀ o : Site2, ξ = oneGrain o →
      ∃ W : List (Finset Site2), ∀ η' : StableField, (∀ x ∈ K, η' x = η x) →
        ((∃ (ws : List (List Site2)) (V : Finset Site2),
            affected (oneGrain o) (listCounts ws.flatten) ⊆ V ∧
              IsWaveStabilization V o (initial η' (oneGrain o)) ws) ∧
          ∀ (ws : List (List Site2)) (V : Finset Site2),
            affected (oneGrain o) (listCounts ws.flatten) ⊆ V →
              IsWaveStabilization V o (initial η' (oneGrain o)) ws →
                ws.map (fun w => (listCounts w).support) = W) ∧
        ∀ V : Finset Site2, K ⊆ V →
          (∃ ws : List (List Site2), IsWaveStabilization V o (initial η' (oneGrain o)) ws) ∧
          ∀ ws : List (List Site2), IsWaveStabilization V o (initial η' (oneGrain o)) ws →
            ws.map (fun w => (listCounts w).support) = W) := by
  have hη' := hη
  obtain ⟨w, hw⟩ := hη'
  have hu : odometer ξ ⟨η, hη⟩ = listCounts w := odometer_eq_counts ξ ⟨η, hη⟩ hw
  intro u K
  have hu' : u = listCounts w := hu
  have hK : K = affected ξ (listCounts w) := by
    show affected ξ u = _
    rw [hu']
  clear_value u K
  subst hu' hK
  refine ⟨fun η' heq => ?_, fun o hξ => ?_⟩
  · obtain ⟨⟨hts, _⟩, hV⟩ := finite_determination_counts hw heq
    refine ⟨⟨⟨η', w, hts⟩, rfl, odometer_eq_counts ξ ⟨η', w, hts⟩ hts⟩, fun V hKV => ?_⟩
    obtain ⟨hWs, huniq⟩ := hV V hKV
    exact ⟨⟨w, hWs⟩, fun v hv => huniq v hv⟩
  · subst hξ
    obtain ⟨ws, hc, _, ht⟩ := exists_determined_wave_stabilization hw
    have hsupp : ∀ a b : List (List Site2), a.map listCounts = b.map listCounts →
        a.map (fun v => (listCounts v).support) = b.map (fun v => (listCounts v).support) := by
      intro a b h
      simpa only [List.map_map, Function.comp_def] using
        congrArg (List.map (fun c : Counts => c.support)) h
    refine ⟨ws.map (fun v => (listCounts v).support), fun η' heq => ?_⟩
    obtain ⟨_, hK, hV⟩ := ht η' heq
    refine ⟨⟨⟨ws, affected (oneGrain o) (listCounts w), by rw [hc], hK⟩, ?_⟩, ?_⟩
    · intro ws2 V2 hV2 hws2
      have hfl := hws2.flatten_stable
      have hstab : Stabilizes η' (oneGrain o) ws2.flatten := by
        refine ⟨hfl.2.1, fun x => ?_⟩
        by_cases hx : x ∈ V2
        · exact hfl.2.2 x hx
        · have hxa : x ∉ affected (oneGrain o) (listCounts ws2.flatten) := fun h => hx (hV2 h)
          have hz := count_zero_outside_affected hxa
          rw [lap_zero_outside_affected hxa]
          simp only [initial, hz.1, Nat.cast_zero, add_zero]
          exact ⟨by positivity, by exact_mod_cast (η' x).isLt⟩
      have hcount : listCounts ws2.flatten = listCounts w :=
        stabilizes_counts_unique hstab (stabilizes_transfer hw heq)
      have hKV2 : affected (oneGrain o) (listCounts w) ⊆ V2 := by
        rw [← hcount]
        exact hV2
      exact hsupp _ _ ((hV V2 hKV2).2 ws2 hws2)
    · intro V hKV
      obtain ⟨htrace, huniq⟩ := hV V hKV
      exact ⟨⟨ws, htrace⟩, fun ws' h' => hsupp _ _ (huniq ws' h')⟩

end
end FiniteAvalanches.Paper.Dynamics
