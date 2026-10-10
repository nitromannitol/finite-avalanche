import FiniteAvalanches.Wilson.Lattice.Law
import FiniteAvalanches.Needle.Statement

set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice
open LatticeProb MeasureTheory
open scoped Classical ENNReal
noncomputable section

private theorem walkErase_zero (x : Site 2) (w : WalkDriver) :
    walkErase x w 0 = [x] := by
  simp [walkErase, eraseStep]

private theorem walkErase_succ (x : Site 2) (w : WalkDriver) (T : ℕ) :
    walkErase x w (T + 1) = eraseStep (walkErase x w T) (position x w (T + 1)) := by
  simp only [walkErase, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

private theorem walkErase_start (x : Site 2) (w : WalkDriver) (T : ℕ) :
    ∃ tail, walkErase x w T = x :: tail := by
  induction T with
  | zero => exact ⟨[], walkErase_zero x w⟩
  | succ T ih =>
    obtain ⟨tail, ht⟩ := ih
    rw [walkErase_succ, ht]
    by_cases he : x = position x w (T + 1)
    · exact ⟨[], by rw [eraseStep, ← he,
        List.takeWhile_cons_of_neg (by simp), List.nil_append]⟩
    · exact ⟨tail.takeWhile (fun u => decide (u ≠ position x w (T + 1))) ++
        [position x w (T + 1)], by
          rw [eraseStep, List.takeWhile_cons_of_pos (by simpa only [decide_eq_true_eq] using he)]
          rfl⟩

private theorem walkErase_end (x : Site 2) (w : WalkDriver) (T : ℕ) :
    ∃ front, walkErase x w T = front ++ [position x w T] := by
  cases T with
  | zero => exact ⟨[], walkErase_zero x w⟩
  | succ T => exact ⟨(walkErase x w T).takeWhile
      (fun u => decide (u ≠ position x w (T + 1))), walkErase_succ x w T⟩

/-- The queried start is retained, excluding the old root endpoint. -/
theorem walkErase_start_mem_dropLast (x : Site 2) (w : WalkDriver) (T : ℕ)
    (hne : x ≠ position x w T) : x ∈ (walkErase x w T).dropLast := by
  obtain ⟨tail, ht⟩ := walkErase_start x w T
  have hx : x ∈ walkErase x w T := by rw [ht]; exact List.mem_cons_self
  obtain ⟨front, hp⟩ := walkErase_end x w T
  rw [hp, List.mem_append, List.mem_singleton] at hx
  rw [hp, List.dropLast_concat]
  exact hx.resolve_right hne

@[simp] theorem initialSampler_covered (R : RootPair) :
    (initialSampler R).covered = R.zero ∪ R.one := by
  ext x
  by_cases h0 : x ∈ R.zero <;> by_cases h1 : x ∈ R.one <;>
    simp [SamplerState.covered, initialSampler, h0, h1]

@[simp] theorem initialSampler_true (R : RootPair) (x : Site 2) :
    (initialSampler R).colors x = some true ↔ x ∈ R.one := by
  by_cases h0 : x ∈ R.zero
  · have h1 : x ∉ R.one := fun h => Set.disjoint_left.mp R.disjoint h0 h
    simp [initialSampler, h0, h1]
  · simp [initialSampler, h0]

private theorem samplerRun_singleton (st : SamplerState) (x : Site 2)
    (ξ : ℕ → WalkDriver) : samplerRun st [x] ξ = samplerStep st x (ξ 0) := by
  cases hs : samplerStep st x (ξ 0) <;> simp [samplerRun, hs]

/-- Ordered hitting is exactly a one-colored least hit of the union. -/
theorem hitBefore_iff_union_hit (R : RootPair) (x : Site 2) (w : WalkDriver) :
    w ∈ hitBefore R.zero R.one x ↔
      ∃ T, hitTime (R.zero ∪ R.one) x w = some T ∧ position x w T ∈ R.one := by
  constructor
  · rintro ⟨n, hn, ha⟩
    have hu : ∃ m, position x w m ∈ R.zero ∪ R.one := ⟨n, Or.inr hn⟩
    have hle : Nat.find hu ≤ n := Nat.find_min' hu (Or.inr hn)
    have h1 : position x w (Nat.find hu) ∈ R.one :=
      (Nat.find_spec hu).resolve_left (ha _ hle)
    exact ⟨Nat.find hu, (hitTime_eq_some_iff _ _ _ _).mpr
      ⟨Nat.find_spec hu, fun m hm => Nat.find_min hu hm⟩, h1⟩
  · rintro ⟨T, hT, h1⟩
    have ht := (hitTime_eq_some_iff _ _ _ _).mp hT
    refine ⟨T, h1, ?_⟩
    intro m hm h0
    rcases lt_or_eq_of_le hm with hlt | rfl
    · exact ht.2 m hlt (Or.inl h0)
    · exact Set.disjoint_left.mp R.disjoint h0 h1

/-- Pointwise sampler identity, including both root colors and nonstopping words. -/
theorem single_sampler_true_iff (R : RootPair) (x : Site 2) (ξ : ℕ → WalkDriver) :
    (∃ st, samplerRun (initialSampler R) [x] ξ = some st ∧ st.colors x = some true) ↔
      ξ 0 ∈ hitBefore R.zero R.one x := by
  rw [samplerRun_singleton]
  by_cases h0 : x ∈ R.zero
  · rw [hitBefore_of_zero_root R h0]
    simp [samplerStep, SamplerState.covered, initialSampler, h0]
  · by_cases h1 : x ∈ R.one
    · rw [hitBefore_of_one_root R h1]
      simp [samplerStep, SamplerState.covered, initialSampler, h0, h1]
    · have hx : x ∉ (initialSampler R).covered := by
        rw [initialSampler_covered]; exact fun h => h.elim h0 h1
      rw [samplerStep, if_neg hx, initialSampler_covered, hitBefore_iff_union_hit]
      cases hT : hitTime (R.zero ∪ R.one) x (ξ 0) with
      | none => simp
      | some T =>
        have ht := (hitTime_eq_some_iff _ _ _ _).mp hT
        have hne : x ≠ position x (ξ 0) T := by
          intro he
          have hu : x ∈ R.zero ∪ R.one := he.symm ▸ ht.1
          exact hu.elim h0 h1
        have hm := walkErase_start_mem_dropLast x (ξ 0) T hne
        simp only [Option.some.injEq]
        simp
        rw [if_pos hm, initialSampler_true]

/-- Single-vertex color marginal of the actual Wilson law, for arbitrary roots. -/
theorem wilsonColorLaw_single_vertex (R : RootPair) (x : Site 2) :
    wilsonColorLaw R {σ | σ x = true} = walkLaw (hitBefore R.zero R.one x) := by
  have h := wilsonColorLaw_apply_sampler R [x] {x} (fun _ => true) (by simp)
  simp only [Finset.mem_singleton, forall_eq] at h
  rw [h]
  have he : {ξ | ∃ st, samplerRun (initialSampler R) [x] ξ = some st ∧
      st.colors x = some true} = (fun ξ : ℕ → WalkDriver => ξ 0) ⁻¹'
        hitBefore R.zero R.one x := by
    ext ξ; exact single_sampler_true_iff R x ξ
  rw [he, ← Measure.map_apply (measurable_pi_apply 0) (measurableSet_hitBefore _ _ _)]
  exact congrArg (fun μ : Measure WalkDriver => μ (hitBefore R.zero R.one x))
    (Measure.infinitePi_map_eval (fun _ : ℕ => walkLaw) 0)

/-- The marginal with genuine first hitting times; infinite avoidance remains top. -/
theorem wilsonColorLaw_single_vertex_firstHit (R : RootPair) (x : Site 2) :
    wilsonColorLaw R {σ | σ x = true} = walkLaw
      {w | firstHit R.one (position x w) < firstHit R.zero (position x w)} := by
  rw [wilsonColorLaw_single_vertex]
  congr 1
  ext w
  exact hitBefore_iff_firstHit_lt _ _ _ _

/-- A one-root hit outside the box forces its FIRST exit before the smaller zero set. -/
theorem hitBefore_subset_firstExit (R : RootPair) (Z : Set (Site 2)) (N : ℕ)
    (hZ : Z ⊆ R.zero) (hC : R.one ⊆ (↑(box 2 N) : Set (Site 2))ᶜ) (x : Site 2) :
    hitBefore R.zero R.one x ⊆
      {w | firstHit (↑(box 2 N) : Set (Site 2))ᶜ (position x w) <
        firstHit Z (position x w)} := by
  rintro w ⟨n, hn, ha⟩
  apply (hitBefore_iff_firstHit_lt Z _ x w).mp
  have hex : ∃ m, position x w m ∈ (↑(box 2 N) : Set (Site 2))ᶜ := ⟨n, hC hn⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro m hm hz
  exact ha m (hm.trans (Nat.find_min' hex (hC hn))) (hZ hz)

/-- Actual color probability is bounded by the true first-exit probability. -/
theorem wilsonColorLaw_single_vertex_le_firstExit (R : RootPair)
    (Z : Set (Site 2)) (N : ℕ) (hZ : Z ⊆ R.zero)
    (hC : R.one ⊆ (↑(box 2 N) : Set (Site 2))ᶜ) (x : Site 2) :
    wilsonColorLaw R {σ | σ x = true} ≤ walkLaw
      {w | firstHit (↑(box 2 N) : Set (Site 2))ᶜ (position x w) <
        firstHit Z (position x w)} := by
  rw [wilsonColorLaw_single_vertex]
  exact measure_mono (hitBefore_subset_firstExit R Z N hZ hC x)

end
end FiniteAvalanches.Wilson.Lattice
#print axioms FiniteAvalanches.Wilson.Lattice.single_sampler_true_iff
#print axioms FiniteAvalanches.Wilson.Lattice.wilsonColorLaw_single_vertex
#print axioms FiniteAvalanches.Wilson.Lattice.wilsonColorLaw_single_vertex_firstHit
#print axioms FiniteAvalanches.Wilson.Lattice.wilsonColorLaw_single_vertex_le_firstExit
