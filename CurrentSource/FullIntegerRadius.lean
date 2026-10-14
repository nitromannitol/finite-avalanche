import CurrentSource.RawFullRadius
import FiniteAvalanches.Sandpile.ExtendedObservables

/-! The source avalanche radius on every integer field; no stability premise. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Sandpile.FullInteger
open LatticeProb LatticeProb.Sandpile FiniteAvalanches Sandpile MeasureTheory
open scoped Classical ENNReal
noncomputable section

abbrev Field := RawFull.Field
abbrev Stabilizes := RawFull.Stabilizes
abbrev initial := RawFull.initial

def FiniteStabilizable (η : Field) (o : Site2) : Prop :=
  ∃ w, Stabilizes η (oneGrain o) w

theorem existsUnique_avalanche_counts {η : Field} {o : Site2}
    (h : FiniteStabilizable η o) :
    ∃! u : Counts, ∃ w, Stabilizes η (oneGrain o) w ∧ listCounts w = u :=
  RawFull.existsUnique_counts h

/-- The full word-count criterion is proved before any one-grain count is chosen. -/
theorem word_counts_iff {η : Field} {o : Site2} {w : List Site2}
    (hw : Stabilizes η (oneGrain o) w) (u : Counts) :
    (∃ v, Stabilizes η (oneGrain o) v ∧ listCounts v = u) ↔ listCounts w = u := by
  constructor
  · rintro ⟨v, hv, he⟩
    exact (RawFull.stabilizes_counts_unique hw hv).trans he
  · intro he
    exact ⟨w, hw, he⟩

theorem existsUnique_counts_iff (η : Field) (o : Site2) :
    (∃! u : Counts, ∃ w, Stabilizes η (oneGrain o) w ∧ listCounts w = u) ↔
      FiniteStabilizable η o := by
  constructor
  · rintro ⟨u, ⟨w, hw, _⟩, _⟩
    exact ⟨w, hw⟩
  · exact existsUnique_avalanche_counts

abbrev StabilizableField (o : Site2) := {η : Field // FiniteStabilizable η o}

def avalancheOdometer (o : Site2) (η : StabilizableField o) : Counts :=
  RawFull.odometer (oneGrain o) ⟨η.val, η.property⟩

theorem avalancheOdometer_full_characterization (o : Site2)
    (η : StabilizableField o) (u : Counts) :
    avalancheOdometer o η = u ↔
      ∃ w, Stabilizes η.val (oneGrain o) w ∧ listCounts w = u :=
  RawFull.odometer_full_characterization (oneGrain o) ⟨η.val, η.property⟩ u

theorem avalancheOdometer_eq_counts (o : Site2) (η : StabilizableField o)
    {w : List Site2} (hw : Stabilizes η.val (oneGrain o) w) :
    avalancheOdometer o η = listCounts w :=
  RawFull.odometer_eq_counts (oneGrain o) ⟨η.val, η.property⟩ hw

theorem avalancheOdometer_word_length (o : Site2) (η : StabilizableField o)
    {w : List Site2} (hw : Stabilizes η.val (oneGrain o) w) :
    (avalancheOdometer o η).sum (fun _ n => n) = w.length := by
  rw [avalancheOdometer_eq_counts o η hw]
  exact listCounts_total w

/-- Maximal positive-support distance, empty zero, and infinity exactly on failure
of finite upper-stable legal stabilization. -/
def radius (η : Field) (o : Site2) : WithTop ℕ :=
  if h : FiniteStabilizable η o then
    (countsRadius o (avalancheOdometer o ⟨η, h⟩) : WithTop ℕ)
  else ⊤

theorem radius_of_stabilizes {η : Field} {o : Site2} {w : List Site2}
    (hw : Stabilizes η (oneGrain o) w) :
    radius η o = (countsRadius o (listCounts w) : WithTop ℕ) := by
  have h : FiniteStabilizable η o := ⟨w, hw⟩
  rw [radius, dif_pos h, avalancheOdometer_eq_counts o ⟨η, h⟩ hw]

theorem radius_eq_top_iff (η : Field) (o : Site2) :
    radius η o = ⊤ ↔ ¬FiniteStabilizable η o := by
  by_cases h : FiniteStabilizable η o <;> simp [radius, h]

theorem radius_of_empty {η : Field} {o : Site2}
    (hw : Stabilizes η (oneGrain o) []) : radius η o = 0 := by
  rw [radius_of_stabilizes hw]
  simp [countsRadius, listCounts_support]

theorem radius_le_iff_exists_word (η : Field) (o : Site2) (R : ℕ) :
    radius η o ≤ (R : WithTop ℕ) ↔
      ∃ w, Stabilizes η (oneGrain o) w ∧ countsRadius o (listCounts w) ≤ R := by
  constructor
  · intro hR
    have hf : FiniteStabilizable η o := by
      by_contra hn
      rw [(radius_eq_top_iff _ _).mpr hn] at hR
      exact WithTop.not_top_le_coe R hR
    obtain ⟨w, hw⟩ := hf
    refine ⟨w, hw, ?_⟩
    rw [radius_of_stabilizes hw] at hR
    exact WithTop.coe_le_coe.mp hR
  · rintro ⟨w, hw, hR⟩
    rw [radius_of_stabilizes hw]
    exact WithTop.coe_le_coe.mpr hR

theorem measurable_eval (x : Site2) : Measurable (fun η : Field => η x) :=
  measurable_pi_apply x

theorem measurableSet_height_test (x : Site2) (P : ℤ → Prop) :
    MeasurableSet {η : Field | P (η x)} :=
  (Set.to_countable {a : ℤ | P a}).measurableSet.preimage (measurable_eval x)

theorem measurableSet_stabilizes (ξ : Counts) (w : List Site2) :
    MeasurableSet {η : Field | Stabilizes η ξ w} := by
  have hl : MeasurableSet {η : Field | LegalList (initial η ξ) w} := by
    simp only [LegalList, Set.setOf_forall]
    apply MeasurableSet.iInter
    intro k
    apply MeasurableSet.iInter
    intro hk
    exact measurableSet_height_test w[k]
      (fun a => 4 ≤ a + (ξ w[k] : ℤ) + lap (prefixCounts w k) w[k])
  have hs : MeasurableSet {η : Field |
      ∀ x, initial η ξ x + lap (fun y => (listCounts w y : ℤ)) x < 4} := by
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro x
    exact measurableSet_height_test x
      (fun a => a + (ξ x : ℤ) + lap (fun y => (listCounts w y : ℤ)) x < 4)
  exact hl.inter hs

theorem measurableSet_finiteStabilizable (o : Site2) :
    MeasurableSet {η : Field | FiniteStabilizable η o} := by
  simp only [FiniteStabilizable, Set.setOf_exists]
  exact MeasurableSet.iUnion fun w => measurableSet_stabilizes (oneGrain o) w

theorem measurableSet_radius_le (o : Site2) (R : ℕ) :
    MeasurableSet {η : Field | radius η o ≤ (R : WithTop ℕ)} := by
  simp_rw [radius_le_iff_exists_word]
  simp only [Set.setOf_exists, Set.setOf_and]
  exact MeasurableSet.iUnion fun w => (measurableSet_stabilizes (oneGrain o) w).inter
    (if h : countsRadius o (listCounts w) ≤ R then by
      simpa only [h, Set.setOf_true] using MeasurableSet.univ
    else by simpa only [h, Set.setOf_false] using MeasurableSet.empty)

theorem real_radius_tail_eq_floor (o : Site2) (R : ℝ) (hR : 0 ≤ R) :
    {η : Field | ENNReal.ofReal R < extendedCount (radius η o)} =
      {η | (⌊R⌋₊ : WithTop ℕ) < radius η o} := by
  ext η
  change ENNReal.ofReal R < extendedCount (radius η o) ↔
    (⌊R⌋₊ : WithTop ℕ) < radius η o
  cases h : radius η o using WithTop.recTopCoe with
  | top => exact iff_of_true ENNReal.ofReal_lt_top (WithTop.coe_lt_top (⌊R⌋₊ : ℕ))
  | coe n =>
    exact (ofReal_lt_extendedCount_coe R hR n).trans
      ((Nat.floor_lt hR).symm.trans WithTop.coe_lt_coe.symm)

theorem measurableSet_real_radius_tail (o : Site2) (R : ℝ) (hR : 0 ≤ R) :
    MeasurableSet {η : Field | ENNReal.ofReal R < extendedCount (radius η o)} := by
  rw [real_radius_tail_eq_floor o R hR]
  simpa only [Set.compl_setOf, not_le] using (measurableSet_radius_le o ⌊R⌋₊).compl

theorem finiteStabilizable_stable_iff (η : RawFull.SourceState) (o : Site2) :
    FiniteStabilizable η.val o ↔ RawFull.FiniteStabilizable η o := Iff.rfl

/-- The old radius is exactly the restriction of the full public carrier. -/
theorem radius_stable_eq (η : RawFull.SourceState) (o : Site2) :
    radius η.val o = RawFull.radius η o := by
  by_cases h : RawFull.FiniteStabilizable η o
  · obtain ⟨w, hw⟩ := h
    rw [radius_of_stabilizes hw, RawFull.radius_of_stabilizes hw]
  · rw [(radius_eq_top_iff _ _).mpr h, (RawFull.radius_eq_top_iff _ _).mpr h]

/-- Every NN comparison goes through the actual stable restriction. -/
theorem radius_nn_eq (η : Sandpile.StableField) (o : Site2) :
    radius (RawFull.nnEmbedding η).val o = FiniteAvalanches.radius η o :=
  (radius_stable_eq (RawFull.nnEmbedding η) o).trans (RawFull.radius_nn_eq η o)

theorem avalancheOdometer_certificate_independent (o : Site2) (η : Field)
    (h k : FiniteStabilizable η o) :
    avalancheOdometer o ⟨η, h⟩ = avalancheOdometer o ⟨η, k⟩ := rfl

theorem radius_finite_characterization (η : Field) (o : Site2) (r : ℕ) :
    radius η o = (r : WithTop ℕ) ↔
      ∃ w, Stabilizes η (oneGrain o) w ∧ countsRadius o (listCounts w) = r := by
  constructor
  · intro hr
    have hf : FiniteStabilizable η o := by
      by_contra hn
      rw [(radius_eq_top_iff _ _).mpr hn] at hr
      exact WithTop.top_ne_coe hr
    obtain ⟨w, hw⟩ := hf
    refine ⟨w, hw, ?_⟩
    rw [radius_of_stabilizes hw] at hr
    exact WithTop.coe_injective hr
  · rintro ⟨w, hw, hr⟩
    rw [radius_of_stabilizes hw, hr]

theorem radius_max_positive_support (o : Site2) (η : StabilizableField o) (r : ℕ) :
    radius η.val o ≤ (r : WithTop ℕ) ↔
      ∀ x, 0 < avalancheOdometer o η x → siteRadius o x ≤ r := by
  rw [radius, dif_pos η.property]
  exact WithTop.coe_le_coe.trans (countsRadius_le_iff o (avalancheOdometer o η) r)

theorem radius_attained (o : Site2) (η : StabilizableField o)
    (h : (avalancheOdometer o η).support.Nonempty) :
    ∃ x, 0 < avalancheOdometer o η x ∧ radius η.val o = (siteRadius o x : WithTop ℕ) := by
  obtain ⟨x, hx, he⟩ := countsRadius_attained o (avalancheOdometer o η) h
  refine ⟨x, hx, ?_⟩
  rw [radius, dif_pos η.property, he]

theorem negative_stabilizes_empty (o : Site2) :
    Stabilizes RawFull.negativeStable.val (oneGrain o) [] :=
  RawFull.negative_stabilizes_empty o

theorem negative_radius_zero (o : Site2) : radius RawFull.negativeStable.val o = 0 :=
  radius_of_empty (negative_stabilizes_empty o)

/-- Sites affected by a finite word: original copies of all four neighbours. -/
def affectedSites (u : Counts) : Finset Site2 :=
  u.support ∪ Finset.univ.biUnion (fun i : Fin 2 =>
    u.support.image (fun y => y - unit i) ∪ u.support.image (fun y => y + unit i))

theorem lap_zero_outside_affected (u : Counts) (x : Site2) (hx : x ∉ affectedSites u) :
    lap (fun y => (u y : ℤ)) x = 0 := by
  have h0 : u x = 0 := by
    by_contra h
    exact hx (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr h))
  have hp (i : Fin 2) : u (x + unit i) = 0 := by
    by_contra hn
    have h := Finsupp.mem_support_iff.mpr hn
    apply hx
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ i, Finset.mem_union_left _ ?_⟩
    exact Finset.mem_image.mpr ⟨x + unit i, h, add_sub_cancel_right x (unit i)⟩
  have hm (i : Fin 2) : u (x - unit i) = 0 := by
    by_contra hn
    have h := Finsupp.mem_support_iff.mpr hn
    apply hx
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ i, Finset.mem_union_right _ ?_⟩
    exact Finset.mem_image.mpr ⟨x - unit i, h, sub_add_cancel x (unit i)⟩
  simp [lap, nbrSumZ, h0, hp, hm]

def constantFour : Field := fun _ => 4

/-- An untouched site remains at least four after every finite word. -/
theorem constantFour_not_finiteStabilizable (o : Site2) :
    ¬FiniteStabilizable constantFour o := by
  rintro ⟨w, hw⟩
  obtain ⟨x, hx⟩ := (affectedSites (listCounts w)).exists_notMem
  have ht := hw.2 x
  rw [lap_zero_outside_affected (listCounts w) x hx] at ht
  have hn : (0 : ℤ) ≤ (oneGrain o x : ℤ) := Nat.cast_nonneg _
  change 4 + (oneGrain o x : ℤ) + 0 < 4 at ht
  omega

theorem constantFour_radius_infinite (o : Site2) : radius constantFour o = ⊤ :=
  (radius_eq_top_iff _ _).mpr (constantFour_not_finiteStabilizable o)

end
end FiniteAvalanches.Sandpile.FullInteger

