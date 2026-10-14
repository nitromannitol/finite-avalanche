import CurrentSource.RawFullStabilization
import FiniteAvalanches.Sandpile.ExtendedObservables

/-! The full upper-stable integer avalanche radius and its exact NN dictionary. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Sandpile.RawFull
open LatticeProb LatticeProb.Sandpile FiniteAvalanches Sandpile MeasureTheory
open scoped Classical ENNReal
noncomputable section

def FiniteStabilizable (η : SourceState) (o : Site2) : Prop :=
  ∃ w, Stabilizes η.val (oneGrain o) w

theorem existsUnique_avalanche_counts {η : SourceState} {o : Site2}
    (h : FiniteStabilizable η o) :
    ∃! u : Counts, ∃ w, Stabilizes η.val (oneGrain o) w ∧ listCounts w = u :=
  existsUnique_counts h

abbrev StabilizableSourceState (o : Site2) := {η : SourceState // FiniteStabilizable η o}

def avalancheOdometer (o : Site2) (η : StabilizableSourceState o) : Counts :=
  odometer (oneGrain o) ⟨η.val.val, η.property⟩

theorem avalancheOdometer_full_characterization (o : Site2)
    (η : StabilizableSourceState o) (u : Counts) :
    avalancheOdometer o η = u ↔
      ∃ w, Stabilizes η.val.val (oneGrain o) w ∧ listCounts w = u :=
  odometer_full_characterization (oneGrain o) ⟨η.val.val, η.property⟩ u

theorem avalancheOdometer_eq_counts (o : Site2) (η : StabilizableSourceState o)
    {w : List Site2} (hw : Stabilizes η.val.val (oneGrain o) w) :
    avalancheOdometer o η = listCounts w :=
  odometer_eq_counts (oneGrain o) ⟨η.val.val, η.property⟩ hw

/-- Maximal positive-support distance, empty zero, and infinity exactly on failure
of finite upper-stable legal stabilization. -/
def radius (η : SourceState) (o : Site2) : WithTop ℕ :=
  if h : FiniteStabilizable η o then
    (countsRadius o (avalancheOdometer o ⟨η, h⟩) : WithTop ℕ)
  else ⊤

theorem radius_of_stabilizes {η : SourceState} {o : Site2} {w : List Site2}
    (hw : Stabilizes η.val (oneGrain o) w) :
    radius η o = (countsRadius o (listCounts w) : WithTop ℕ) := by
  have h : FiniteStabilizable η o := ⟨w, hw⟩
  rw [radius, dif_pos h, avalancheOdometer_eq_counts o ⟨η, h⟩ hw]

theorem radius_eq_top_iff (η : SourceState) (o : Site2) :
    radius η o = ⊤ ↔ ¬FiniteStabilizable η o := by
  by_cases h : FiniteStabilizable η o <;> simp [radius, h]

theorem radius_of_empty {η : SourceState} {o : Site2}
    (hw : Stabilizes η.val (oneGrain o) []) : radius η o = 0 := by
  rw [radius_of_stabilizes hw]
  simp [countsRadius, listCounts_support]

theorem finiteStabilizable_nn_iff (η : Sandpile.StableField) (o : Site2) :
    FiniteStabilizable (nnEmbedding η) o ↔ FiniteAvalanches.FiniteStabilizable η o :=
  exists_congr fun w => stabilizes_nn_iff η (oneGrain o) w

theorem radius_nn_eq (η : Sandpile.StableField) (o : Site2) :
    radius (nnEmbedding η) o = FiniteAvalanches.radius η o := by
  by_cases h : FiniteAvalanches.FiniteStabilizable η o
  · obtain ⟨w, hw⟩ := h
    rw [radius_of_stabilizes ((stabilizes_nn_iff _ _ _).mpr hw),
      FiniteAvalanches.radius_of_stabilizes hw]
  · rw [(radius_eq_top_iff _ _).mpr (fun hp => h ((finiteStabilizable_nn_iff _ _).mp hp)),
      (FiniteAvalanches.radius_eq_top_iff _ _).mpr h]

theorem radius_nn_encoding_eq (η : SourceState) (h : Nonnegative η) (o : Site2) :
    radius η o = FiniteAvalanches.radius (nnEncoding η h) o := by
  calc
    _ = radius (nnEmbedding (nnEncoding η h)) o :=
      congrArg (fun ζ => radius ζ o) (nnEmbedding_nnEncoding η h).symm
    _ = _ := radius_nn_eq _ _

theorem radius_le_iff_exists_word (η : SourceState) (o : Site2) (R : ℕ) :
    radius η o ≤ (R : WithTop ℕ) ↔
      ∃ w, Stabilizes η.val (oneGrain o) w ∧ countsRadius o (listCounts w) ≤ R := by
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

theorem measurable_eval (x : Site2) : Measurable (fun η : SourceState => η.val x) :=
  (measurable_pi_apply x).comp measurable_subtype_coe

theorem measurableSet_height_test (x : Site2) (P : ℤ → Prop) :
    MeasurableSet {η : SourceState | P (η.val x)} :=
  (Set.to_countable {a : ℤ | P a}).measurableSet.preimage (measurable_eval x)

theorem measurableSet_stabilizes (ξ : Counts) (w : List Site2) :
    MeasurableSet {η : SourceState | Stabilizes η.val ξ w} := by
  have hl : MeasurableSet {η : SourceState | LegalList (initial η.val ξ) w} := by
    simp only [LegalList, Set.setOf_forall]
    apply MeasurableSet.iInter
    intro k
    apply MeasurableSet.iInter
    intro hk
    exact measurableSet_height_test w[k]
      (fun a => 4 ≤ a + (ξ w[k] : ℤ) + lap (prefixCounts w k) w[k])
  have hs : MeasurableSet {η : SourceState |
      ∀ x, initial η.val ξ x + lap (fun y => (listCounts w y : ℤ)) x < 4} := by
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro x
    exact measurableSet_height_test x
      (fun a => a + (ξ x : ℤ) + lap (fun y => (listCounts w y : ℤ)) x < 4)
  exact hl.inter hs

theorem measurableSet_finiteStabilizable (o : Site2) :
    MeasurableSet {η : SourceState | FiniteStabilizable η o} := by
  simp only [FiniteStabilizable, Set.setOf_exists]
  exact MeasurableSet.iUnion fun w => measurableSet_stabilizes (oneGrain o) w

theorem measurableSet_radius_le (o : Site2) (R : ℕ) :
    MeasurableSet {η : SourceState | radius η o ≤ (R : WithTop ℕ)} := by
  simp_rw [radius_le_iff_exists_word]
  simp only [Set.setOf_exists, Set.setOf_and]
  exact MeasurableSet.iUnion fun w => (measurableSet_stabilizes (oneGrain o) w).inter
    (if h : countsRadius o (listCounts w) ≤ R then by
      simpa only [h, Set.setOf_true] using MeasurableSet.univ
    else by simpa only [h, Set.setOf_false] using MeasurableSet.empty)

theorem real_radius_tail_eq_floor (o : Site2) (R : ℝ) (hR : 0 ≤ R) :
    {η : SourceState | ENNReal.ofReal R < extendedCount (radius η o)} =
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
    MeasurableSet {η : SourceState | ENNReal.ofReal R < extendedCount (radius η o)} := by
  rw [real_radius_tail_eq_floor o R hR]
  simpa only [Set.compl_setOf, not_le] using (measurableSet_radius_le o ⌊R⌋₊).compl

def negativeStable : SourceState := ⟨fun _ => -1, fun _ => by norm_num⟩

theorem negative_stabilizes_empty (o : Site2) :
    Stabilizes negativeStable.val (oneGrain o) [] := by
  constructor
  · intro k hk
    simp only [List.length_nil, Nat.not_lt_zero] at hk
  · intro x
    by_cases hx : x = o
    · subst x
      simp [initial, negativeStable, oneGrain, listCounts, lap, nbrSumZ]
    · simp [initial, negativeStable, oneGrain, listCounts, lap, nbrSumZ, hx]

theorem negative_radius_zero (o : Site2) : radius negativeStable o = 0 :=
  radius_of_empty (negative_stabilizes_empty o)

theorem negative_not_nn_encoding : ¬∃ η : Sandpile.StableField, nnEmbedding η = negativeStable := by
  rintro ⟨η, h⟩
  have he := congrFun (congrArg Subtype.val h) (0 : Site2)
  have hn : (0 : ℤ) ≤ (η (0 : Site2)).val := Nat.cast_nonneg _
  change ((η (0 : Site2)).val : ℤ) = -1 at he
  omega

end
end FiniteAvalanches.Sandpile.RawFull

#print axioms FiniteAvalanches.Sandpile.RawFull.avalancheOdometer_full_characterization
#print axioms FiniteAvalanches.Sandpile.RawFull.radius_nn_eq
#print axioms FiniteAvalanches.Sandpile.RawFull.radius_eq_top_iff
#print axioms FiniteAvalanches.Sandpile.RawFull.measurableSet_real_radius_tail
#print axioms FiniteAvalanches.Sandpile.RawFull.negative_radius_zero
#print axioms FiniteAvalanches.Sandpile.RawFull.negative_not_nn_encoding
