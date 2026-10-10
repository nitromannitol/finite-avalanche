import FiniteAvalanches.Wilson.Lattice.Beurling

set_option autoImplicit false
namespace FiniteAvalanches.BeurlingConnected
open LatticeProb MeasureTheory FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.External.Beurling
open scoped Classical ENNReal
noncomputable section

private theorem direction_sup_le_one (a : FiniteAvalanches.Sandpile.FiniteWired.Direction) :
    supNorm (FiniteAvalanches.Sandpile.FiniteWired.step a) ≤ 1 := by
  rcases a with ⟨i, b⟩
  fin_cases i <;> cases b <;>
    simp [FiniteAvalanches.Sandpile.FiniteWired.step, supNorm, unit,
      show (Finset.univ : Finset (Fin 2)) = {0, 1} from by decide]

/-- Exact full stopped-prefix semantics, including a terminal root or TOP for no hit. -/
theorem prefix_avoidance_iff (R : Set (Site 2)) (p : ℕ → Site 2) (t : ℕ) :
    (∀ s < t, p s ∉ R) ↔ (t : WithTop ℕ) ≤ firstHit R p := by
  by_cases hex : ∃ n, p n ∈ R
  · rw [firstHit, dif_pos hex]
    constructor
    · intro hav
      have ht : t ≤ Nat.find hex := by
        by_contra hn
        exact hav (Nat.find hex) (Nat.lt_of_not_ge hn) (Nat.find_spec hex)
      exact_mod_cast ht
    · intro ht s hs
      have ht' : t ≤ Nat.find hex := by exact_mod_cast ht
      exact Nat.find_min hex (hs.trans_le ht')
  · rw [firstHit, dif_neg hex]
    constructor
    · intro _; exact le_top
    · intro _ s _ hs; exact hex ⟨s, hs⟩

/-- If the full stopped walk leaves B_h, its predecessor already strictly exits
B_(h-1) before the first root hit. Ordinary nearest-neighbor positions are used. -/
theorem stopped_exit_subset (R : Set (Site 2)) (x : Site 2) (r h : ℕ)
    (hx : FiniteAvalanches.siteRadius 0 x ≤ r) (hr : r ≤ h) (hh : 1 ≤ h) :
    {ω : WalkDriver | ∃ t : ℕ, h < FiniteAvalanches.siteRadius 0 (position x ω t) ∧
        (t : WithTop ℕ) ≤ firstHit R (position x ω)} ⊆
      hitBefore R {z | h - 1 < FiniteAvalanches.siteRadius 0 z} x := by
  rintro ω ⟨t, ht, hav⟩
  have havoid := (prefix_avoidance_iff R (position x ω) t).mpr hav
  have htpos : 0 < t := by
    by_contra hn
    have he : t = 0 := by omega
    subst t
    simp only [position_zero] at ht
    omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt htpos)
  change h < FiniteAvalanches.siteRadius 0 (position x ω (m + 1)) at ht
  have hstep : supNorm (position x ω (m + 1)) ≤ supNorm (position x ω m) + 1 := by
    rw [position_succ]
    exact (supNorm_triangle _ _).trans
      (Nat.add_le_add_left (direction_sup_le_one (ω m)) _)
  rw [supNorm_eq_siteRadius, supNorm_eq_siteRadius] at hstep
  refine ⟨m, ?_, ?_⟩
  · change h - 1 < FiniteAvalanches.siteRadius 0 (position x ω m)
    omega
  · intro s hs
    exact havoid s (by omega)

private theorem repaired_sqrt_bound (h : ℕ) (hh : 2 ≤ h) (a : ℝ) (ha : 0 ≤ a) :
    Real.sqrt (a / ((h - 1 : ℕ) : ℝ)) ≤ Real.sqrt 2 * Real.sqrt (a / h) := by
  have he : (h - 1 : ℕ) + 1 = h := by omega
  have hr := congrArg (fun n : ℕ => (n : ℝ)) he
  have h2 : (2 : ℝ) ≤ h := by exact_mod_cast hh
  push_cast at hr
  have hhalf : (h : ℝ) / 2 ≤ ((h - 1 : ℕ) : ℝ) := by linarith
  have hd : 0 < ((h - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < h - 1 by omega)
  have hp : 0 < (h : ℝ) := by positivity
  have hdiv : a / ((h - 1 : ℕ) : ℝ) ≤ 2 * (a / h) := by
    apply (div_le_iff₀ hd).mpr
    have hi : 2 * (a / h) * ((h - 1 : ℕ) : ℝ) =
        (2 * a * ((h - 1 : ℕ) : ℝ)) / h := by ring
    rw [hi]
    apply (le_div_iff₀ hp).mpr
    nlinarith
  calc _ ≤ Real.sqrt (2 * (a / h)) := Real.sqrt_le_sqrt hdiv
    _ = _ := Real.sqrt_mul (by norm_num) _

/-- Uniform localization of full stopped traces at roots containing a connected obstacle. -/
theorem full_stopped_localization_bound : ∃ D : ℝ, 0 < D ∧
    ∀ K : Set (Site 2), ((lattice 2).induce K).Preconnected → (0 : Site 2) ∈ K →
    ∀ R : Set (Site 2), K ⊆ R →
    ∀ r h : ℕ, 4 * r + 4 ≤ h - 1 →
      (∃ z ∈ K, FiniteAvalanches.siteRadius 0 z = h - 1) →
    ∀ x : Site 2, FiniteAvalanches.siteRadius 0 x ≤ r →
      FiniteAvalanches.Wilson.Lattice.walkLaw {ω | ∃ t : ℕ, h < FiniteAvalanches.siteRadius 0 (position x ω t) ∧
        (t : WithTop ℕ) ≤ firstHit R (position x ω)} ≤
        ENNReal.ofReal (D * Real.sqrt (((r + 1 : ℕ) : ℝ) / h)) := by
  obtain ⟨C, hC, hbound⟩ := connected_square_exit_bound
  let D : ℝ := C * Real.sqrt 2
  refine ⟨D, mul_pos hC (by positivity), ?_⟩
  intro K hK h0 R hKR r h hscale hboundary x hx
  have hh : 2 ≤ h := by omega
  have hsub := stopped_exit_subset R x r h hx (by omega) (by omega)
  have hmono : hitBefore R {z | h - 1 < FiniteAvalanches.siteRadius 0 z} x ⊆
      hitBefore K {z | h - 1 < FiniteAvalanches.siteRadius 0 z} x := by
    rintro ω ⟨t, ht, hav⟩
    exact ⟨t, ht, fun s hs hmem => hav s hs (hKR hmem)⟩
  have hb := hbound K hK h0 r (h - 1) hscale hboundary x hx
  have hs := repaired_sqrt_bound
    h hh (((r + 1 : ℕ) : ℝ)) (by positivity)
  have hscalar : C * Real.sqrt (((r + 1 : ℕ) : ℝ) / ((h - 1 : ℕ) : ℝ)) ≤
      D * Real.sqrt (((r + 1 : ℕ) : ℝ) / h) := by
    calc _ ≤ C * (Real.sqrt 2 * Real.sqrt (((r + 1 : ℕ) : ℝ) / h)) :=
        mul_le_mul_of_nonneg_left hs hC.le
      _ = _ := by dsimp [D]; ring
  exact (measure_mono (hsub.trans hmono)).trans
    (hb.trans (ENNReal.ofReal_le_ofReal hscalar))

end
end FiniteAvalanches.BeurlingConnected
