import FiniteAvalanches.Model.LegalLists

/-! Literal one-grain avalanche observables on the square lattice. -/

namespace FiniteAvalanches

open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open scoped Classical

/-- One natural-valued grain at the specified source. -/
noncomputable def oneGrain (o : Site2) : Counts := Finsupp.single o 1

theorem initial_oneGrain (η : StableField) (o x : Site2) :
    initial η (oneGrain o) x = ((η x).val : ℤ) + dirac o x := by
  by_cases h : x = o <;> simp [initial, oneGrain, dirac, h]

/-- Existence of a finite ordered legal list stabilizing the one-grain input. -/
def FiniteStabilizable (η : StableField) (o : Site2) : Prop :=
  ∃ w : List Site2, Stabilizes η (oneGrain o) w

theorem existsUnique_odometer {η : StableField} {o : Site2}
    (h : FiniteStabilizable η o) :
    ∃! u : Counts, ∃ w, Stabilizes η (oneGrain o) w ∧ listCounts w = u :=
  existsUnique_counts h

/-- The exact domain on which the one-grain odometer exists. -/
abbrev StabilizableField (o : Site2) := {η : StableField // FiniteStabilizable η o}

/-- The unique finite natural count, using the already proved list-count uniqueness. -/
noncomputable def avalancheOdometer (o : Site2) (η : StabilizableField o) : Counts :=
  odometer (oneGrain o) η

theorem avalancheOdometer_spec (o : Site2) (η : StabilizableField o) :
    ∃ w, Stabilizes η.val (oneGrain o) w ∧ listCounts w = avalancheOdometer o η :=
  odometer_spec (oneGrain o) η

theorem avalancheOdometer_eq_counts (o : Site2) (η : StabilizableField o)
    {w : List Site2} (hw : Stabilizes η.val (oneGrain o) w) :
    avalancheOdometer o η = listCounts w :=
  odometer_eq_counts (oneGrain o) η hw

/-- The integer lattice sup distance, represented in naturals without rounding. -/
def siteRadius (o x : Site2) : ℕ :=
  Finset.univ.sup (fun i : Fin 2 => (x i - o i).natAbs)

theorem siteRadius_le_iff (o x : Site2) (r : ℕ) :
    siteRadius o x ≤ r ↔ ∀ i : Fin 2, |x i - o i| ≤ (r : ℤ) := by
  simp only [siteRadius, Finset.sup_le_iff, Finset.mem_univ, forall_const]
  apply forall_congr'
  intro i
  rw [← Int.natCast_natAbs]
  exact (Nat.cast_le (α := ℤ)).symm

/-- Maximum radius of the positive count support; the empty maximum is zero. -/
noncomputable def countsRadius (o : Site2) (u : Counts) : ℕ :=
  u.support.sup (siteRadius o)

theorem countsRadius_le_iff (o : Site2) (u : Counts) (r : ℕ) :
    countsRadius o u ≤ r ↔ ∀ x, 0 < u x → siteRadius o x ≤ r := by
  simp only [countsRadius, Finset.sup_le_iff, Finsupp.mem_support_iff, Nat.pos_iff_ne_zero]

theorem countsRadius_attained (o : Site2) (u : Counts) (hu : u.support.Nonempty) :
    ∃ x, 0 < u x ∧ countsRadius o u = siteRadius o x := by
  obtain ⟨x, hx, he⟩ := Finset.sup_mem_of_nonempty (f := siteRadius o) hu
  exact ⟨x, Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hx), he.symm⟩

/-- Source radius, with infinity exactly when no finite legal stabilization exists. -/
noncomputable def radius (η : StableField) (o : Site2) : WithTop ℕ :=
  if h : FiniteStabilizable η o then
    (countsRadius o (avalancheOdometer o ⟨η, h⟩) : WithTop ℕ)
  else ⊤

/-- Source total topplings, with the same infinity convention. -/
noncomputable def totalTopplings (η : StableField) (o : Site2) : WithTop ℕ :=
  if h : FiniteStabilizable η o then
    (((avalancheOdometer o ⟨η, h⟩).sum (fun _ n => n) : ℕ) : WithTop ℕ)
  else ⊤

theorem radius_of_stabilizes {η : StableField} {o : Site2} {w : List Site2}
    (hw : Stabilizes η (oneGrain o) w) :
    radius η o = (countsRadius o (listCounts w) : WithTop ℕ) := by
  have h : FiniteStabilizable η o := ⟨w, hw⟩
  simp only [radius, dif_pos h]
  rw [avalancheOdometer_eq_counts o ⟨η, h⟩ hw]

theorem totalTopplings_of_stabilizes {η : StableField} {o : Site2} {w : List Site2}
    (hw : Stabilizes η (oneGrain o) w) :
    totalTopplings η o = (w.length : WithTop ℕ) := by
  have h : FiniteStabilizable η o := ⟨w, hw⟩
  simp only [totalTopplings, dif_pos h]
  rw [avalancheOdometer_eq_counts o ⟨η, h⟩ hw, listCounts_total]

theorem radius_eq_top_iff (η : StableField) (o : Site2) :
    radius η o = ⊤ ↔ ¬ FiniteStabilizable η o := by
  by_cases h : FiniteStabilizable η o <;> simp [radius, h]

theorem totalTopplings_eq_top_iff (η : StableField) (o : Site2) :
    totalTopplings η o = ⊤ ↔ ¬ FiniteStabilizable η o := by
  by_cases h : FiniteStabilizable η o
  · rw [totalTopplings, dif_pos h]
    exact iff_of_false WithTop.coe_ne_top (not_not.mpr h)
  · rw [totalTopplings, dif_neg h]
    exact iff_of_true rfl h

theorem radius_of_empty {η : StableField} {o : Site2}
    (hw : Stabilizes η (oneGrain o) []) : radius η o = 0 := by
  rw [radius_of_stabilizes hw]
  simp [countsRadius, listCounts_support]

theorem totalTopplings_of_empty {η : StableField} {o : Site2}
    (hw : Stabilizes η (oneGrain o) []) : totalTopplings η o = 0 := by
  simpa using totalTopplings_of_stabilizes hw

theorem list_observables_eq {η : StableField} {o : Site2} {w v : List Site2}
    (hw : Stabilizes η (oneGrain o) w) (hv : Stabilizes η (oneGrain o) v) :
    countsRadius o (listCounts w) = countsRadius o (listCounts v) ∧ w.length = v.length := by
  have hc := stabilizes_counts_unique hw hv
  refine ⟨congrArg (countsRadius o) hc, ?_⟩
  rw [← listCounts_total w, ← listCounts_total v, hc]

theorem measurableSet_height_test (x : Site2) (P : Fin 4 → Prop) :
    MeasurableSet {η : StableField | P (η x)} :=
  (Set.toFinite {a : Fin 4 | P a}).measurableSet.preimage (measurable_pi_apply x)

theorem stableField_borelSpace : BorelSpace StableField := inferInstance

theorem measurableSet_stabilizes (ξ : Counts) (w : List Site2) :
    MeasurableSet {η : StableField | Stabilizes η ξ w} := by
  have hl : MeasurableSet {η : StableField | LegalList (initial η ξ) w} := by
    simp only [LegalList, Set.setOf_forall]
    apply MeasurableSet.iInter
    intro k
    apply MeasurableSet.iInter
    intro hk
    exact measurableSet_height_test w[k]
      (fun a => 4 ≤ (a.val : ℤ) + (ξ w[k] : ℤ) + lap (prefixCounts w k) w[k])
  have hf : MeasurableSet {η : StableField | ∀ x,
      0 ≤ initial η ξ x + lap (fun y => (listCounts w y : ℤ)) x ∧
        initial η ξ x + lap (fun y => (listCounts w y : ℤ)) x < 4} := by
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro x
    exact measurableSet_height_test x (fun a =>
      0 ≤ (a.val : ℤ) + (ξ x : ℤ) + lap (fun y => (listCounts w y : ℤ)) x ∧
        (a.val : ℤ) + (ξ x : ℤ) + lap (fun y => (listCounts w y : ℤ)) x < 4)
  exact hl.inter hf

theorem measurableSet_finiteStabilizable (o : Site2) :
    MeasurableSet {η : StableField | FiniteStabilizable η o} := by
  simp only [FiniteStabilizable, Set.setOf_exists]
  exact MeasurableSet.iUnion (fun w => measurableSet_stabilizes (oneGrain o) w)


end FiniteAvalanches
