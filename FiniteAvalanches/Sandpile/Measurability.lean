import FiniteAvalanches.Sandpile.Observables

/-! Measurability and finite fibers of the literal one-grain observables. -/

namespace FiniteAvalanches
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile

theorem empty_singleton_stabilizes (η : StableField) (o : Site2)
    (h : (η o).val ≤ 2) : Stabilizes η (oneGrain o) [] := by
  rw [stabilizes_iff_legal_and_lt]
  constructor
  · intro k hk
    simp at hk
  · intro x
    by_cases he : x = o
    · subst x
      have ho : ((η o).val : ℤ) ≤ 2 := by exact_mod_cast h
      simpa [initial, oneGrain, listCounts, lap, nbrSumZ] using (by omega :
        ((η o).val : ℤ) + 1 < 4)
    · simp [initial, oneGrain, listCounts, lap, nbrSumZ, he]

theorem empty_singleton_observables (η : StableField) (o : Site2)
    (h : (η o).val ≤ 2) : radius η o = 0 ∧ totalTopplings η o = 0 :=
  ⟨radius_of_empty (empty_singleton_stabilizes η o h),
    totalTopplings_of_empty (empty_singleton_stabilizes η o h)⟩

theorem measurableSet_every_source :
    MeasurableSet {η : StableField | ∀ o, FiniteStabilizable η o} := by
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter measurableSet_finiteStabilizable

theorem radius_fiber (o : Site2) (n : ℕ) :
    (fun η : StableField => radius η o) ⁻¹' {(n : WithTop ℕ)} =
      ⋃ w : List Site2, {η | Stabilizes η (oneGrain o) w ∧
        countsRadius o (listCounts w) = n} := by
  ext η
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · intro h
    have hf : FiniteStabilizable η o := by
      by_contra hn
      rw [(radius_eq_top_iff η o).mpr hn] at h
      exact WithTop.top_ne_coe h
    obtain ⟨w, hw⟩ := hf
    refine ⟨w, hw, ?_⟩
    rw [radius_of_stabilizes hw] at h
    exact WithTop.coe_inj.mp h
  · rintro ⟨w, hw, hn⟩
    rw [radius_of_stabilizes hw, hn]

theorem totalTopplings_fiber (o : Site2) (n : ℕ) :
    (fun η : StableField => totalTopplings η o) ⁻¹' {(n : WithTop ℕ)} =
      ⋃ w : List Site2, {η | Stabilizes η (oneGrain o) w ∧ w.length = n} := by
  ext η
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · intro h
    have hf : FiniteStabilizable η o := by
      by_contra hn
      rw [(totalTopplings_eq_top_iff η o).mpr hn] at h
      exact WithTop.top_ne_coe h
    obtain ⟨w, hw⟩ := hf
    refine ⟨w, hw, ?_⟩
    rw [totalTopplings_of_stabilizes hw] at h
    exact WithTop.coe_inj.mp h
  · rintro ⟨w, hw, hn⟩
    rw [totalTopplings_of_stabilizes hw, hn]

theorem measurable_radius (o : Site2) : Measurable (fun η : StableField => radius η o) := by
  apply measurable_to_countable'
  intro n
  cases n using WithTop.recTopCoe with
  | top =>
    have he : (fun η : StableField => radius η o) ⁻¹' {⊤} =
        {η : StableField | FiniteStabilizable η o}ᶜ := by
      ext η
      exact radius_eq_top_iff η o
    rw [he]
    exact (measurableSet_finiteStabilizable o).compl
  | coe n =>
    change MeasurableSet ((fun η : StableField => radius η o) ⁻¹' {(n : WithTop ℕ)})
    rw [radius_fiber o n]
    exact MeasurableSet.iUnion fun w =>
      (measurableSet_stabilizes (oneGrain o) w).inter (MeasurableSet.const _)

theorem measurable_totalTopplings (o : Site2) :
    Measurable (fun η : StableField => totalTopplings η o) := by
  apply measurable_to_countable'
  intro n
  cases n using WithTop.recTopCoe with
  | top =>
    have he : (fun η : StableField => totalTopplings η o) ⁻¹' {⊤} =
        {η : StableField | FiniteStabilizable η o}ᶜ := by
      ext η
      exact totalTopplings_eq_top_iff η o
    rw [he]
    exact (measurableSet_finiteStabilizable o).compl
  | coe n =>
    change MeasurableSet ((fun η : StableField => totalTopplings η o) ⁻¹' {(n : WithTop ℕ)})
    rw [totalTopplings_fiber o n]
    exact MeasurableSet.iUnion fun w =>
      (measurableSet_stabilizes (oneGrain o) w).inter (MeasurableSet.const _)


end FiniteAvalanches
