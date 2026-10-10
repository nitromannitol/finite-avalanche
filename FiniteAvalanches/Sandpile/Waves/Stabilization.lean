import FiniteAvalanches.Sandpile.Waves.LegalLists

/-! Complete finite stabilizations run as successive legal source waves. -/

namespace FiniteAvalanches.Sandpile.Waves

open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile FiniteAvalanches
open scoped Classical

noncomputable section

/-- The literal height after the listed single-site topplings. -/
def heightAfter (s : Site2 → ℤ) (w : List Site2) : Site2 → ℤ :=
  fun x => s x + lap (fun y => (listCounts w y : ℤ)) x

theorem list_counts_append_int (a b : List Site2) :
    (fun x => (listCounts (a ++ b) x : ℤ)) =
      fun x => (listCounts a x : ℤ) + (listCounts b x : ℤ) := by
  funext x
  simp [listCounts_apply, List.count_append]

theorem height_after_append (s : Site2 → ℤ) (a b : List Site2) :
    heightAfter s (a ++ b) = heightAfter (heightAfter s a) b := by
  funext x
  simp only [heightAfter, list_counts_append_int, lap_add]
  ring

theorem height_after_nil (s : Site2 → ℤ) : heightAfter s [] = s := by
  funext x
  simp [heightAfter, listCounts, lap, nbrSumZ]

theorem legal_list_append {s : Site2 → ℤ} {a b : List Site2}
    (ha : LegalList s a) (hb : LegalList (heightAfter s a) b) : LegalList s (a ++ b) := by
  intro k hk
  by_cases hka : k < a.length
  · have ht : prefixCounts (a ++ b) k = prefixCounts a k := by
      funext x
      simp only [prefixCounts, List.take_append_of_le_length (Nat.le_of_lt hka)]
    simpa only [List.getElem_append_left hka, ht] using ha k hka
  · have hka' : a.length ≤ k := by omega
    have hkb : k - a.length < b.length := by simp only [List.length_append] at hk; omega
    have ht : prefixCounts (a ++ b) k =
        fun x => (listCounts a x : ℤ) + prefixCounts b (k - a.length) x := by
      funext x
      simp only [prefixCounts, List.take_append, List.take_of_length_le hka',
        List.count_append, Nat.cast_add, listCounts_apply]
    rw [List.getElem_append_right hka', ht, lap_add]
    have h := hb (k - a.length) hkb
    dsimp [heightAfter] at h
    linarith

/-- A trace of complete source waves, ending exactly when every active site is stable. -/
inductive IsWaveStabilization (V : Finset Site2) (o : Site2) :
    (Site2 → ℤ) → List (List Site2) → Prop
  | nil {s} (hs : ∀ x ∈ V, 0 ≤ s x ∧ s x < 4) : IsWaveStabilization V o s []
  | cons {s v ws} (hoV : o ∈ V) (ho : 4 ≤ s o) (hv : ∀ x ∈ v, x ∈ V ∧ x ≠ o)
      (hl : LegalList s (o :: v))
      (hs : ∀ x ∈ V, x ≠ o → 0 ≤ heightAfter s (o :: v) x ∧ heightAfter s (o :: v) x < 4)
      (ht : IsWaveStabilization V o (heightAfter s (o :: v)) ws) :
      IsWaveStabilization V o s ((o :: v) :: ws)

theorem IsWaveStabilization.flatten_stable {V : Finset Site2} {o : Site2}
    {s : Site2 → ℤ} {ws : List (List Site2)} (h : IsWaveStabilization V o s ws)
    :
    (∀ x ∈ ws.flatten, x ∈ V) ∧ LegalList s ws.flatten ∧
      ∀ x ∈ V, 0 ≤ heightAfter s ws.flatten x ∧ heightAfter s ws.flatten x < 4 := by
  induction h with
  | nil hs =>
    refine ⟨by simp, by intro k hk; simp at hk, ?_⟩
    simpa only [List.flatten_nil, height_after_nil] using hs
  | @cons s v ws hoV hsrc hv hl hs ht ih =>
    simp only [List.flatten_cons]
    refine ⟨?_, legal_list_append hl ih.2.1, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact hoV
        · exact (hv x hx).1
      · exact ih.1 x hx
    · rw [height_after_append]
      exact ih.2.2

/-- The complete one-grain wired avalanche admits a finite ordered wave trace. -/
theorem exists_wave_stabilization (η : StableField) (o : Site2) (R : ℕ)
    (hoR : o ∈ boxSites R) :
    ∃ ws : List (List Site2),
      IsWaveStabilization (boxSites R) o (initial η (oneGrain o)) ws ∧
      WiredStabilizes η (oneGrain o) (boxSites R) ws.flatten := by
  let s := initial η (oneGrain o)
  let B := 8 * (R + 1)^4
  have bound {p : List Site2} (hp : LegalList s p) (hpR : ∀ x ∈ p, x ∈ boxSites R) :
      p.length ≤ B := (one_grain_legal_list_box_bound η o R hp hpR).2
  have go : ∀ n : ℕ, ∀ p : List Site2, B - p.length = n →
      LegalList s p → (∀ x ∈ p, x ∈ boxSites R) →
      (∀ x ∈ boxSites R, x ≠ o → heightAfter s p x < 4) →
      ∃ ws, IsWaveStabilization (boxSites R) o (heightAfter s p) ws := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hn hp hpR hpOff
      have hnonneg : ∀ x, 0 ≤ heightAfter s p x := by
        intro x
        have h := hp.heights_nonneg (initial_nonneg η (oneGrain o)) p.length x
        rw [prefix_eq_terminal p p.length le_rfl] at h
        exact h
      by_cases hsrc : heightAfter s p o < 4
      · refine ⟨[], IsWaveStabilization.nil (fun x hx => ⟨hnonneg x, ?_⟩)⟩
        by_cases hxo : x = o
        · simpa only [hxo] using hsrc
        · exact hpOff x hx hxo
      · obtain ⟨v, hv, hl, _, _, hvOff⟩ := exists_legal_wave (heightAfter s p) R
          (boxSites R) o (Finset.Subset.refl _) hoR (by omega) hnonneg
          (fun x hx hxo => by have h := hpOff x hx hxo; omega)
        let p' := p ++ (o :: v)
        have hp' : LegalList s p' := legal_list_append hp hl
        have hpR' : ∀ x ∈ p', x ∈ boxSites R := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hpR x hx
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact hoR
            · exact (hv x hx).1
        have hb := bound hp' hpR'
        have hlen : p'.length = p.length + v.length + 1 := by simp [p', Nat.add_assoc]
        have hlt : B - p'.length < n := by omega
        have hnext : ∀ x ∈ boxSites R, x ≠ o → heightAfter s p' x < 4 := by
          rw [show heightAfter s p' = heightAfter (heightAfter s p) (o :: v) from
            height_after_append s p (o :: v)]
          exact fun x hx hxo => (hvOff x hx hxo).2
        obtain ⟨ws, hws⟩ := ih (B - p'.length) hlt p' rfl hp' hpR' hnext
        rw [show heightAfter s p' = heightAfter (heightAfter s p) (o :: v) from
          height_after_append s p (o :: v)] at hws
        exact ⟨(o :: v) :: ws, IsWaveStabilization.cons hoR (by omega) hv hl hvOff hws⟩
  have h0 : LegalList s [] := by intro k hk; simp at hk
  obtain ⟨ws, hws⟩ := go B [] (by simp) h0 (by simp) (by
    rw [height_after_nil]
    intro x _ hxo
    dsimp [s]
    rw [initial_oneGrain, dirac_of_ne hxo, add_zero]
    exact_mod_cast (η x).isLt)
  rw [height_after_nil] at hws
  have hf := hws.flatten_stable
  exact ⟨ws, hws, hf⟩

end
end FiniteAvalanches.Sandpile.Waves
