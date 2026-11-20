import FiniteAvalanches.Walk.Beurling.Defs
import FiniteAvalanches.Walk.IidBlocks
import LatticeProb.Prob.ZeroOne

/-!
# The product formula for the strip exit of the Beurling estimate

For the simple random walk on `ℤ²` started at the origin, the probability of leaving the strip
`{|Im z| < n}` before a positive-time visit to the real axis factors as the probability of
leaving it before a visit to the negative axis times the probability of leaving it before a
visit to the non-positive axis. This is Lemma 9 of G. F. Lawler and V. Limic, *The Beurling
estimate for a class of random walks*, Electron. J. Probab. 9 (2004), for `κ = 1`; the step
distribution is symmetric, so it is its own reversal.

The proof follows the paper. A walk that avoids the non-positive axis but meets the positive axis
before leaving the strip is split at the last visit to the smallest positive point visited; the
piece after that time is a walk of the same kind, by the Markov property at a fixed time. The
piece before it is reversed and negated, and that is the walk up to its first visit to the
negative axis. Summing over the time of the split gives the probability of that first visit,
which is the complement of the leaving event, since the walk leaves the strip almost surely.

## Main statements

* `measurePreserving_revNeg`: reversing and negating the first `j` increments preserves the
  law of the walk.
* `markov_split`: an event that depends on the first `j` increments is independent of the
  increments after time `j`.
* `strip_axis_product`: the product formula.
-/

noncomputable section

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb
open MeasureTheory ProbabilityTheory

/-! ### The walk from the origin -/

theorem walkPos_zero_succ (ω : ℕ → Dir 2) (t : ℕ) :
    walkPos 0 ω (t + 1) = walkPos 0 ω t + dirVec (ω t) := by
  simp [walkPos, Finset.sum_range_succ]

/-- The increments after time `j`. -/
def shiftBy (j : ℕ) (ω : ℕ → Dir 2) : ℕ → Dir 2 := fun i => ω (j + i)

/-- The walk at time `j + t` is its position at time `j` plus the walk driven by the increments
after time `j`. -/
theorem walkPos_zero_add (ω : ℕ → Dir 2) (j t : ℕ) :
    walkPos 0 ω (j + t) = walkPos 0 ω j + walkPos 0 (shiftBy j ω) t := by
  simp [walkPos, shiftBy, Finset.sum_range_add]

/-- Coordinatewise form of `walkPos_zero_add`. -/
theorem walkPos_add_apply (ω : ℕ → Dir 2) (j t : ℕ) (c : Fin 2) :
    walkPos 0 ω (j + t) c = walkPos 0 ω j c + walkPos 0 (shiftBy j ω) t c := by
  rw [walkPos_zero_add]; rfl

/-- The first `j` positions of the walk are determined by the first `j` increments. -/
theorem walkPos_congr {ω ω' : ℕ → Dir 2} {j : ℕ} (h : ∀ i < j, ω i = ω' i) {t : ℕ}
    (ht : t ≤ j) : walkPos 0 ω t = walkPos 0 ω' t := by
  unfold walkPos
  congr 1
  exact Finset.sum_congr rfl fun i hi => by rw [h i (by have := Finset.mem_range.mp hi; omega)]

/-! ### The Markov property at a fixed time -/

/-- An event that is decided by the first `j` increments. -/
def DependsOnFirst (j : ℕ) (A : Set (ℕ → Dir 2)) : Prop :=
  ∀ ω ω' : ℕ → Dir 2, (∀ i < j, ω i = ω' i) → (ω ∈ A ↔ ω' ∈ A)

/-- An event decided by the first `j` increments is a preimage under `take 2 j`. -/
theorem DependsOnFirst.eq_preimage {j : ℕ} {A : Set (ℕ → Dir 2)} (h : DependsOnFirst j A) :
    A = take 2 j ⁻¹' (take 2 j '' A) := by
  ext ω
  refine ⟨fun hω => ⟨ω, hω, rfl⟩, ?_⟩
  rintro ⟨ω', hω', he⟩
  exact (h ω' ω fun i hi => by simpa [take] using congrFun he ⟨i, hi⟩).1 hω'

/-- An event decided by the first `j` increments is measurable. -/
theorem DependsOnFirst.measurableSet {j : ℕ} {A : Set (ℕ → Dir 2)} (h : DependsOnFirst j A) :
    MeasurableSet A := by
  rw [h.eq_preimage]
  exact measurable_take 2 j (Set.toFinite _).measurableSet

/-- Dropping the first `j` increments preserves the law of the walk. -/
theorem measurePreserving_shiftBy (j : ℕ) :
    MeasurePreserving (shiftBy j) (pathLaw 2) (pathLaw 2) :=
  measurePreserving_coordShift (fun _ => stepLaw 2) (fun a b h => by simpa using h) fun _ => rfl

/-- A map into a product is measurable for a `σ`-algebra as soon as each coordinate is. -/
theorem comap_le_of_coordinates {ι α X : Type*} [MeasurableSpace X] {m : MeasurableSpace α}
    (f : α → ι → X) (h : ∀ k, MeasurableSpace.comap (fun a => f a k) inferInstance ≤ m) :
    MeasurableSpace.comap f inferInstance ≤ m := by
  rw [show (inferInstance : MeasurableSpace (ι → X)) =
      ⨆ k, MeasurableSpace.comap (fun x : ι → X => x k) inferInstance from rfl,
    MeasurableSpace.comap_iSup]
  refine iSup_le fun k => ?_
  rw [MeasurableSpace.comap_comp]
  exact h k

/-- The first `j` increments are independent of the increments after time `j`. -/
theorem indepFun_take_shiftBy (j : ℕ) :
    IndepFun (take 2 j) (shiftBy j) (pathLaw 2) := by
  classical
  let s : ℕ → MeasurableSpace (ℕ → Dir 2) := fun i =>
    MeasurableSpace.comap (fun ω : ℕ → Dir 2 => ω i) inferInstance
  have hle : ∀ i, s i ≤ (inferInstance : MeasurableSpace (ℕ → Dir 2)) := fun i =>
    (measurable_pi_apply i).comap_le
  have hind : iIndep s (pathLaw 2) := (iIndepFun_iff_iIndep _ _ _).mp (iIndepFun_pathLaw 2)
  have hd : Disjoint {i : ℕ | i < j} {i : ℕ | j ≤ i} :=
    Set.disjoint_left.mpr fun _ h1 h2 => Nat.not_lt_of_ge h2 h1
  have hsplit := indep_iSup_of_disjoint hle hind hd
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hsplit ?_) ?_
  · refine comap_le_of_coordinates _ fun k => ?_
    exact le_biSup s (show (k : ℕ) ∈ {i : ℕ | i < j} from k.2)
  · refine comap_le_of_coordinates _ fun k => ?_
    exact le_biSup s (show j + k ∈ {i : ℕ | j ≤ i} from Nat.le_add_right _ _)

/-- An event decided by the first `j` increments is independent of the increments after
time `j`, which have the law of the whole walk. -/
theorem markov_split {j : ℕ} {A B : Set (ℕ → Dir 2)} (hA : DependsOnFirst j A)
    (hB : MeasurableSet B) :
    pathLaw 2 (A ∩ shiftBy j ⁻¹' B) = pathLaw 2 A * pathLaw 2 B := by
  have hV : MeasurableSet (take 2 j '' A) := (Set.toFinite _).measurableSet
  have h := (indepFun_take_shiftBy j).measure_inter_preimage_eq_mul _ _ hV hB
  rw [← hA.eq_preimage] at h
  rw [h, (measurePreserving_shiftBy j).measure_preimage hB.nullMeasurableSet]

/-! ### Reversal of the path -/

/-- The index of the increment that takes the place of increment `i` when the first `j` are
reversed. -/
def revIdx (j i : ℕ) : ℕ := if i < j then j - 1 - i else i

/-- Reversing the first `j` coordinates twice is the identity. -/
theorem revIdx_revIdx (j i : ℕ) : revIdx j (revIdx j i) = i := by
  unfold revIdx; split_ifs <;> omega

/-- The opposite direction. -/
def negDir (a : Dir 2) : Dir 2 := (a.1, !a.2)

/-- The unit vector of the opposite direction is the negative of the unit vector. -/
theorem dirVec_negDir (a : Dir 2) : dirVec (negDir a) = -dirVec a := by
  funext k
  by_cases h : k = a.1 <;> cases hb : a.2 <;> simp [negDir, dirVec, h, hb]

/-- Reversing a direction twice is the identity. -/
theorem negDir_negDir (a : Dir 2) : negDir (negDir a) = a := by simp [negDir]

/-- A uniform direction reversed is a uniform direction. -/
theorem map_negDir : (stepLaw 2).map negDir = stepLaw 2 := by
  refine Measure.ext_of_singleton fun a => ?_
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton a)]
  have : negDir ⁻¹' {a} = {negDir a} := by
    ext b
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => by rw [← h, negDir_negDir], fun h => by rw [h, negDir_negDir]⟩
  rw [this, stepLaw_singleton, stepLaw_singleton]

/-- Reverse the first `j` increments and negate every increment. -/
def revNeg (j : ℕ) (ω : ℕ → Dir 2) : ℕ → Dir 2 := fun i => negDir (ω (revIdx j i))

/-- The path reversal: reversing and negating the first `j` increments of the simple random
walk preserves its law. -/
theorem measurePreserving_revNeg (j : ℕ) :
    MeasurePreserving (revNeg j) (pathLaw 2) (pathLaw 2) := by
  have h1 : MeasurePreserving (coordShift (X := Dir 2) (revIdx j)) (pathLaw 2) (pathLaw 2) :=
    measurePreserving_coordShift (fun _ => stepLaw 2)
      (Function.LeftInverse.injective (revIdx_revIdx j)) fun _ => rfl
  have h2 : MeasurePreserving (fun (ω : ℕ → Dir 2) (i : ℕ) => negDir (ω i))
      (pathLaw 2) (pathLaw 2) := by
    refine ⟨measurable_pi_lambda _ fun i =>
      (measurable_of_countable negDir).comp (measurable_pi_apply i), ?_⟩
    rw [pathLaw, Measure.infinitePi_map_pi _ (fun _ => measurable_of_countable negDir)]
    simp only [map_negDir]
  exact h2.comp h1

/-- The position of the reversed and negated walk at time `k ≤ j`. -/
theorem walkPos_revNeg (ω : ℕ → Dir 2) (j : ℕ) {k : ℕ} (hk : k ≤ j) :
    walkPos 0 (revNeg j ω) k = walkPos 0 ω (j - k) - walkPos 0 ω j := by
  induction k with
  | zero => simp [walkPos]
  | succ k ih =>
    have hkj : k < j := by omega
    have e1 : j - k = (j - (k + 1)) + 1 := by omega
    have e2 : walkPos 0 ω (j - k) = walkPos 0 ω (j - (k + 1)) + dirVec (ω (j - 1 - k)) := by
      rw [e1, walkPos_zero_succ]
      congr 3
      omega
    have e3 : revNeg j ω k = negDir (ω (j - 1 - k)) := by simp [revNeg, revIdx, hkj]
    rw [walkPos_zero_succ, ih (by omega), e3, dirVec_negDir, e2]
    abel

/-! ### The events -/

theorem mem_stripExitsBefore_iff (n : ℕ) (B : Set (Site 2)) (ω : ℕ → Dir 2) :
    ω ∈ stripExitsBefore (n : ℝ) B 0 ↔
      ∃ t, (n : ℤ) ≤ |walkPos 0 ω t 1| ∧ ∀ s, 1 ≤ s → s ≤ t → walkPos 0 ω s ∉ B := by
  unfold stripExitsBefore
  simp only [Set.mem_setOf_eq]
  refine exists_congr fun t => and_congr ?_ Iff.rfl
  rw [← Int.cast_abs]
  exact_mod_cast Iff.rfl

/-- Enlarging `B` shrinks the event `{ρ_r < T_B}`. -/
theorem stripExitsBefore_anti {B B' : Set (Site 2)} (h : B ⊆ B') (r : ℝ) (x : Site 2) :
    stripExitsBefore r B' x ⊆ stripExitsBefore r B x :=
  fun _ ⟨t, ht, hs⟩ => ⟨t, ht, fun s h₁ h₂ hB => hs s h₁ h₂ (h hB)⟩

/-- The walks that, before leaving the strip, visit the positive axis for the last time at the
smallest positive point they visit, at time `j`, and avoid the points up to it before that. -/
def splitBefore (n j : ℕ) : Set (ℕ → Dir 2) :=
  {ω | 1 ≤ j ∧ walkPos 0 ω j 1 = 0 ∧ 1 ≤ walkPos 0 ω j 0 ∧
    (∀ i, 1 ≤ i → i ≤ j → walkPos 0 ω i ∉ axisSet {z | z ≤ walkPos 0 ω j 0 - 1}) ∧
    ∀ i, i ≤ j → |walkPos 0 ω i 1| < n}

/-- The walks whose first visit to the negative axis is at time `j`, before leaving the strip. -/
def firstNegHit (n j : ℕ) : Set (ℕ → Dir 2) :=
  {ω | 1 ≤ j ∧ walkPos 0 ω j ∈ axisSet {z | z < 0} ∧
    (∀ i, 1 ≤ i → i < j → walkPos 0 ω i ∉ axisSet {z | z < 0}) ∧
    ∀ i, i ≤ j → |walkPos 0 ω i 1| < n}

/-- Whether the split happens at time `j` is decided by the first `j` increments. -/
theorem dependsOnFirst_splitBefore (n j : ℕ) : DependsOnFirst j (splitBefore n j) := by
  intro ω ω' h
  have hw : ∀ i, i ≤ j → walkPos 0 ω i = walkPos 0 ω' i := fun i hi => walkPos_congr h hi
  simp (config := {contextual := true}) only [splitBefore, Set.mem_setOf_eq, hw, le_refl]

/-- Whether the first visit to the negative axis is at time `j` is decided by the first `j`
increments. -/
theorem dependsOnFirst_firstNegHit (n j : ℕ) : DependsOnFirst j (firstNegHit n j) := by
  intro ω ω' h
  have hw : ∀ i, i ≤ j → walkPos 0 ω i = walkPos 0 ω' i := fun i hi => walkPos_congr h hi
  have hw' : ∀ i, i < j → walkPos 0 ω i = walkPos 0 ω' i := fun i hi => hw i hi.le
  simp (config := {contextual := true}) only [firstNegHit, Set.mem_setOf_eq, hw, hw', le_refl]

/-- A walk split at time `j`, followed by a walk that leaves the strip before the non-positive
axis, avoids the non-positive axis until it leaves the strip and meets the axis before. -/
theorem splitBefore_inter_subset (n j : ℕ) :
    splitBefore n j ∩ shiftBy j ⁻¹' stripExitsBefore (n : ℝ) (axisSet {z | z ≤ 0}) 0 ⊆
      stripExitsBefore (n : ℝ) (axisSet {z | z ≤ 0}) 0 \
        stripExitsBefore (n : ℝ) (axisSet Set.univ) 0 := by
  rintro ω ⟨⟨hj, hj1, hj0, hav, hstrip⟩, hshift⟩
  rw [Set.mem_preimage, mem_stripExitsBefore_iff] at hshift
  obtain ⟨t, ht, hs⟩ := hshift
  refine ⟨?_, ?_⟩
  · rw [mem_stripExitsBefore_iff]
    refine ⟨j + t, ?_, ?_⟩
    · rw [walkPos_add_apply, hj1, zero_add]; exact ht
    · intro s hs1 hs2 hmem
      by_cases hsj : s ≤ j
      · refine hav s hs1 hsj ⟨hmem.1, ?_⟩
        have := hmem.2
        simp only [Set.mem_setOf_eq] at this ⊢
        omega
      · obtain ⟨s', rfl⟩ : ∃ s', s = j + s' := ⟨s - j, by omega⟩
        refine hs s' (by omega) (by omega) ⟨?_, ?_⟩
        · have := hmem.1
          rw [walkPos_add_apply, hj1] at this
          simpa using this
        · have := hmem.2
          simp only [Set.mem_setOf_eq] at this ⊢
          rw [walkPos_add_apply] at this
          omega
  · rw [mem_stripExitsBefore_iff]
    rintro ⟨T, hT, hTs⟩
    by_cases hTj : j ≤ T
    · exact hTs j hj hTj ⟨hj1, trivial⟩
    · exact absurd hT (not_le.mpr (hstrip T (by omega)))

/-- A walk that leaves the strip before the non-positive axis but not before the whole axis is
split at some time `j`, at the last visit to the smallest positive point it visits. -/
theorem diff_subset_iUnion {n : ℕ} (hn : 1 ≤ n) :
    stripExitsBefore (n : ℝ) (axisSet {z | z ≤ 0}) 0 \
        stripExitsBefore (n : ℝ) (axisSet Set.univ) 0 ⊆
      ⋃ j, splitBefore n j ∩ shiftBy j ⁻¹' stripExitsBefore (n : ℝ) (axisSet {z | z ≤ 0}) 0 := by
  classical
  rintro ω ⟨hEm, hE⟩
  rw [mem_stripExitsBefore_iff] at hEm hE
  obtain ⟨t0, ht0, hs0⟩ := hEm
  have hex : ∃ t, (n : ℤ) ≤ |walkPos 0 ω t 1| := ⟨t0, ht0⟩
  have hρspec : (n : ℤ) ≤ |walkPos 0 ω (Nat.find hex) 1| := Nat.find_spec hex
  have hρmin : ∀ i < Nat.find hex, |walkPos 0 ω i 1| < n := fun i hi =>
    not_le.mp (Nat.find_min hex hi)
  have hρle : Nat.find hex ≤ t0 := Nat.find_min' hex ht0
  set ρ := Nat.find hex with hρ
  have hρpos : 1 ≤ ρ := by
    rcases Nat.eq_zero_or_pos ρ with h | h
    · rw [h] at hρspec
      simp [walkPos] at hρspec
      omega
    · exact h
  have hno : ∀ s, 1 ≤ s → s ≤ ρ → walkPos 0 ω s ∉ axisSet {z | z ≤ 0} := fun s h1 h2 =>
    hs0 s h1 (by omega)
  have hvis : ∃ s, 1 ≤ s ∧ s ≤ ρ ∧ walkPos 0 ω s 1 = 0 := by
    by_contra hcon
    push Not at hcon
    exact hE ⟨ρ, hρspec, fun s h1 h2 hmem => hcon s h1 h2 hmem.1⟩
  let P : Finset ℕ := (Finset.Icc 1 ρ).filter fun s => walkPos 0 ω s 1 = 0
  have hmemP : ∀ s, s ∈ P ↔ 1 ≤ s ∧ s ≤ ρ ∧ walkPos 0 ω s 1 = 0 := fun s => by
    simp [P, and_assoc]
  have hPne : P.Nonempty := by
    obtain ⟨s, h1, h2, h3⟩ := hvis
    exact ⟨s, (hmemP s).2 ⟨h1, h2, h3⟩⟩
  obtain ⟨s0, hs0P, hs0min⟩ := P.exists_min_image (fun s => walkPos 0 ω s 0) hPne
  let Q : Finset ℕ := P.filter fun s => ∀ s' ∈ P, walkPos 0 ω s 0 ≤ walkPos 0 ω s' 0
  have hmemQ : ∀ s, s ∈ Q ↔ s ∈ P ∧ ∀ s' ∈ P, walkPos 0 ω s 0 ≤ walkPos 0 ω s' 0 := fun s => by
    simp [Q]
  have hQne : Q.Nonempty := ⟨s0, (hmemQ s0).2 ⟨hs0P, hs0min⟩⟩
  have hjQ : Q.max' hQne ∈ Q := Q.max'_mem hQne
  obtain ⟨hjP, hjmin⟩ := (hmemQ _).1 hjQ
  obtain ⟨hj1, hjρ, hjaxis⟩ := (hmemP _).1 hjP
  set j := Q.max' hQne with hj
  have hlast : ∀ s', 1 ≤ s' → s' ≤ ρ → walkPos 0 ω s' 1 = 0 →
      walkPos 0 ω s' 0 = walkPos 0 ω j 0 → s' ≤ j := by
    intro s' h1 h2 h3 h4
    have hs'P : s' ∈ P := (hmemP s').2 ⟨h1, h2, h3⟩
    exact Q.le_max' s' ((hmemQ s').2 ⟨hs'P, fun s'' hs'' => h4 ▸ hjmin s'' hs''⟩)
  have hjlt : j < ρ := by
    rcases hjρ.lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 : walkPos 0 ω ρ 1 = 0 := h ▸ hjaxis
      rw [h1] at hρspec
      simp at hρspec
      omega
  have hjpos : 1 ≤ walkPos 0 ω j 0 := by
    have := hno j hj1 hjρ
    by_contra hcon
    exact this ⟨hjaxis, by simp only [Set.mem_setOf_eq]; omega⟩
  refine Set.mem_iUnion.2 ⟨j, ⟨⟨hj1, hjaxis, hjpos, ?_, ?_⟩, ?_⟩⟩
  · intro i hi1 hij hmem
    have hiP : i ∈ P := (hmemP i).2 ⟨hi1, by omega, hmem.1⟩
    have h1 := hjmin i hiP
    have h2 := hmem.2
    simp only [Set.mem_setOf_eq] at h2
    omega
  · intro i hi
    exact hρmin i (by omega)
  · rw [Set.mem_preimage, mem_stripExitsBefore_iff]
    refine ⟨ρ - j, ?_, ?_⟩
    · have := walkPos_add_apply ω j (ρ - j) 1
      rw [show j + (ρ - j) = ρ by omega, hjaxis, zero_add] at this
      rw [← this]
      exact hρspec
    · intro s hs1 hs2 hmem
      have h1 := walkPos_add_apply ω j s 1
      have h0 := walkPos_add_apply ω j s 0
      have hm1 := hmem.1
      have hm2 := hmem.2
      simp only [Set.mem_setOf_eq] at hm2
      have hjsP : j + s ∈ P := (hmemP _).2 ⟨by omega, by omega, by rw [h1, hjaxis, hm1]; simp⟩
      have := hjmin (j + s) hjsP
      have := hlast (j + s) (by omega) (by omega) (by rw [h1, hjaxis, hm1]; simp) (by omega)
      omega

/-- The split time of a walk is unique. -/
theorem disjoint_pieces {n j j' : ℕ} (hjj : j < j') :
    Disjoint
      (splitBefore n j ∩ shiftBy j ⁻¹' stripExitsBefore (n : ℝ) (axisSet {z | z ≤ 0}) 0)
      (splitBefore n j' ∩ shiftBy j' ⁻¹' stripExitsBefore (n : ℝ) (axisSet {z | z ≤ 0}) 0) := by
  refine Set.disjoint_left.2 fun ω ⟨⟨hj, hj1, hj0, hav, hstrip⟩, hshift⟩
    ⟨⟨hj', hj1', hj0', hav', hstrip'⟩, _⟩ => ?_
  rw [Set.mem_preimage, mem_stripExitsBefore_iff] at hshift
  obtain ⟨t, ht, hs⟩ := hshift
  have htj : j' < j + t := by
    by_contra hcon
    have h1 := hstrip' (j + t) (by omega)
    have h2 := walkPos_add_apply ω j t 1
    rw [hj1, zero_add] at h2
    rw [h2] at h1
    exact absurd ht (not_le.mpr h1)
  have hnot := hav' j hj (by omega)
  have h1 := walkPos_add_apply ω j (j' - j) 1
  have h0 := walkPos_add_apply ω j (j' - j) 0
  rw [show j + (j' - j) = j' by omega] at h1 h0
  refine hs (j' - j) (by omega) (by omega) ⟨?_, ?_⟩
  · rw [hj1', hj1] at h1
    omega
  · simp only [Set.mem_setOf_eq]
    by_contra hcon
    exact hnot ⟨hj1, by simp only [Set.mem_setOf_eq]; omega⟩

/-- Coordinatewise form of `walkPos_revNeg`. -/
theorem walkPos_revNeg_apply (ω : ℕ → Dir 2) (j : ℕ) {k : ℕ} (hk : k ≤ j) (c : Fin 2) :
    walkPos 0 (revNeg j ω) k c = walkPos 0 ω (j - k) c - walkPos 0 ω j c := by
  rw [walkPos_revNeg ω j hk]; rfl

/-- The walk from the origin is at the origin at time `0`. -/
theorem walkPos_zero_zero (ω : ℕ → Dir 2) : walkPos 0 ω 0 = 0 := by simp [walkPos]

/-- Reversing and negating the first `j` increments turns a walk of the first kind into one of
the second. -/
theorem revNeg_preimage_firstNegHit (n j : ℕ) :
    revNeg j ⁻¹' firstNegHit n j = splitBefore n j := by
  ext ω
  have hT := fun k (hk : k ≤ j) c => walkPos_revNeg_apply ω j hk c
  have hTj : ∀ c, walkPos 0 (revNeg j ω) j c = - walkPos 0 ω j c := fun c => by
    rw [hT j le_rfl c, Nat.sub_self, walkPos_zero_zero]; simp
  simp only [Set.mem_preimage, firstNegHit, splitBefore, Set.mem_setOf_eq, axisSet]
  constructor
  · rintro ⟨hj, ⟨h1, h2⟩, h3, h4⟩
    rw [hTj] at h1 h2
    refine ⟨hj, by omega, by omega, ?_, ?_⟩
    · intro i hi1 hij ⟨hm1, hm2⟩
      by_cases hij' : i = j
      · subst hij'; omega
      · refine h3 (j - i) (by omega) (by omega) ⟨?_, ?_⟩
        · rw [hT _ (by omega), show j - (j - i) = i by omega]; omega
        · rw [hT _ (by omega), show j - (j - i) = i by omega]; omega
    · intro i hi
      have := h4 (j - i) (by omega)
      rw [hT _ (by omega)] at this
      have h1' : walkPos 0 ω j 1 = 0 := by omega
      rw [show j - (j - i) = i by omega] at this
      rwa [h1', sub_zero] at this
  · rintro ⟨hj, h1, h2, h3, h4⟩
    refine ⟨hj, ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hTj]; simp [h1]
    · rw [hTj]; omega
    · intro i hi1 hij ⟨hm1, hm2⟩
      rw [hT _ (by omega)] at hm1 hm2
      refine h3 (j - i) (by omega) (by omega) ⟨?_, ?_⟩
      · omega
      · omega
    · intro i hi
      have := h4 (j - i) (by omega)
      rw [hT _ (by omega), h1, sub_zero]
      exact this

/-- The first visit to the negative axis happens at one time only. -/
theorem disjoint_firstNegHit {n j j' : ℕ} (hjj : j < j') :
    Disjoint (firstNegHit n j) (firstNegHit n j') := by
  refine Set.disjoint_left.2 fun ω ⟨hj, hm, _, _⟩ ⟨_, _, hf, _⟩ => ?_
  exact hf j hj hjj hm

/-! ### The walk leaves the strip -/

theorem exists_mem_union_of_exists {n : ℕ} (hn : 1 ≤ n) (ω : ℕ → Dir 2)
    (h : ∃ t, (n : ℤ) ≤ |walkPos 0 ω t 1|) :
    ω ∈ stripExitsBefore (n : ℝ) (axisSet {z | z < 0}) 0 ∪ ⋃ j, firstNegHit n j := by
  classical
  have hρspec : (n : ℤ) ≤ |walkPos 0 ω (Nat.find h) 1| := Nat.find_spec h
  have hρmin : ∀ i < Nat.find h, |walkPos 0 ω i 1| < n := fun i hi =>
    not_le.mp (Nat.find_min h hi)
  set ρ := Nat.find h
  by_cases hvis : ∃ s, 1 ≤ s ∧ s ≤ ρ ∧ walkPos 0 ω s ∈ axisSet {z | z < 0}
  · right
    refine Set.mem_iUnion.2 ⟨Nat.find hvis, ?_⟩
    obtain ⟨hj1, hjρ, hjm⟩ := Nat.find_spec hvis
    have hjlt : Nat.find hvis < ρ := by
      rcases hjρ.lt_or_eq with h' | h'
      · exact h'
      · rw [h'] at hjm
        have := hjm.1
        rw [this] at hρspec
        simp at hρspec
        omega
    refine ⟨hj1, hjm, fun i hi1 hij hmem => ?_, fun i hi => hρmin i (by omega)⟩
    exact Nat.find_min hvis hij ⟨hi1, by omega, hmem⟩
  · left
    rw [mem_stripExitsBefore_iff]
    refine ⟨ρ, hρspec, fun s hs1 hs2 hmem => hvis ⟨s, hs1, hs2, hmem⟩⟩

/-- Leaving the strip before the negative axis excludes visiting the negative axis first. -/
theorem disjoint_strip_firstNegHit (n : ℕ) :
    Disjoint (stripExitsBefore (n : ℝ) (axisSet {z | z < 0}) 0) (⋃ j, firstNegHit n j) := by
  refine Set.disjoint_left.2 fun ω hE hH => ?_
  rw [mem_stripExitsBefore_iff] at hE
  obtain ⟨t, ht, hs⟩ := hE
  obtain ⟨j, hj, hm, _, hstrip⟩ := Set.mem_iUnion.1 hH
  by_cases hjt : j ≤ t
  · exact hs j hj hjt hm
  · exact absurd ht (not_le.mpr (hstrip t (by omega)))

/-! ### The walk leaves the strip almost surely -/

theorem walkPos_upBlock (ω : ℕ → Dir 2) (k L : ℕ)
    (h : ∀ i < L, ω (k * L + i) = ((1 : Fin 2), true)) (i : ℕ) (hi : i ≤ L) :
    walkPos 0 ω (k * L + i) 1 = walkPos 0 ω (k * L) 1 + i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [show k * L + (i + 1) = (k * L + i) + 1 from rfl, walkPos_zero_succ,
      Pi.add_apply, ih (by omega), h i (by omega)]
    simp [dirVec]
    ring

/-- A block of `2 * n` upward steps takes the walk out of the strip of half-width `n`. -/
theorem exists_strip_exit_of_upBlock {n : ℕ} (ω : ℕ → Dir 2) (k : ℕ)
    (h : ∀ i < 2 * n, ω (k * (2 * n) + i) = ((1 : Fin 2), true)) :
    ∃ t, (n : ℤ) ≤ |walkPos 0 ω t 1| := by
  have h1 := walkPos_upBlock ω k (2 * n) h (2 * n) le_rfl
  by_cases hk : (n : ℤ) ≤ |walkPos 0 ω (k * (2 * n)) 1|
  · exact ⟨_, hk⟩
  · refine ⟨k * (2 * n) + 2 * n, ?_⟩
    have h2 := not_le.mp hk
    have h3 := neg_abs_le (walkPos 0 ω (k * (2 * n)) 1)
    have h4 := le_abs_self (walkPos 0 ω (k * (2 * n) + 2 * n) 1)
    push_cast at h1
    linarith

/-- The walk leaves the strip almost surely, so it either leaves it before visiting the negative
axis or visits the negative axis before leaving it. -/
theorem measure_compl_strip_union_eq_zero {n : ℕ} (hn : 1 ≤ n) :
    pathLaw 2 (stripExitsBefore (n : ℝ) (axisSet {z | z < 0}) 0 ∪ ⋃ j, firstNegHit n j)ᶜ = 0 := by
  refine FiniteAvalanches.Walk.IidBlocks.measure_eq_zero_of_subset_avoidsConstantBlocks (stepLaw 2)
    ((1 : Fin 2), true) (2 * n) ?_ _ ?_
  · rw [stepLaw_singleton]; simp
  · intro N ω hω k hk hblock
    exact hω (exists_mem_union_of_exists hn ω (exists_strip_exit_of_upBlock ω k hblock))

/-! ### The product formula -/

theorem measurable_shiftBy (j : ℕ) : Measurable (shiftBy j) :=
  (measurePreserving_shiftBy j).measurable

/-- The measure bookkeeping of the proof of the product formula: if `Em ∖ E` is the disjoint
union of the pieces `V j`, whose measures are those of `H j` times that of `Em`, and the sets
`H j` fill the complement of `Ez` up to a null set, then `μ E = μ Ez * μ Em`. -/
theorem measure_product_aux {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {E Em Ez : Set α} {H V : ℕ → Set α}
    (hE : MeasurableSet E) (hEz : MeasurableSet Ez) (hH : ∀ j, MeasurableSet (H j))
    (hV : ∀ j, MeasurableSet (V j)) (hsub : E ⊆ Em) (hdiff : Em \ E = ⋃ j, V j)
    (hVdisj : Pairwise (Function.onFun Disjoint V)) (hVmeas : ∀ j, μ (V j) = μ (H j) * μ Em)
    (hHdisj : Pairwise (Function.onFun Disjoint H)) (hEzH : Disjoint Ez (⋃ j, H j))
    (hcover : μ (Ez ∪ ⋃ j, H j)ᶜ = 0) :
    (μ E).toReal = (μ Ez).toReal * (μ Em).toReal := by
  have h1 : μ Em = μ (⋃ j, V j) + μ E := by
    rw [← hdiff, ← measure_union Set.disjoint_sdiff_left hE, Set.sdiff_union_of_subset hsub]
  rw [measure_iUnion hVdisj hV] at h1
  simp only [hVmeas, ENNReal.tsum_mul_right] at h1
  rw [(measure_iUnion hHdisj hH).symm] at h1
  have hHm : MeasurableSet (⋃ j, H j) := MeasurableSet.iUnion hH
  have h3 : μ (⋃ j, H j) + μ Ez = 1 := by
    have h := (prob_compl_eq_zero_iff (hEz.union hHm)).1 hcover
    rwa [Set.union_comm, measure_union hEzH.symm hEz] at h
  have e1 := congrArg ENNReal.toReal h1
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
    (measure_ne_top _ _), ENNReal.toReal_mul] at e1
  have e2 := congrArg ENNReal.toReal h3
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ENNReal.toReal_one] at e2
  linear_combination (-1 : ℝ) * e1 + (-(μ Em).toReal) * e2

/-- **Product formula for the strip exit** ([Lawler-Limic 2004], Lemma 9, with `κ = 1` and
`p* = p`): leaving the strip of half-width `n` before a positive-time visit to the real axis
has the probability of leaving it before a visit to the negative axis times the probability of
leaving it before a visit to the non-positive axis. -/
theorem strip_axis_product (n : ℕ) :
    prob (stripExitsBefore n (axisSet Set.univ) 0) =
      prob (stripExitsBefore n (axisSet {j | j < 0}) 0) *
        prob (stripExitsBefore n (axisSet {j | j ≤ 0}) 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h : ∀ B : Set (Site 2), stripExitsBefore ((0 : ℕ) : ℝ) B 0 = Set.univ := fun B =>
      Set.eq_univ_of_forall fun ω => ⟨0, by simp, fun s h1 h2 => absurd h2 (by omega)⟩
    simp only [h, prob, measure_univ, ENNReal.toReal_one, mul_one]
  · have hEm : MeasurableSet (stripExitsBefore (n : ℝ) (axisSet {j | j ≤ 0}) 0) :=
      measurableSet_stripExitsBefore _ _ _
    refine measure_product_aux (pathLaw 2) (H := fun j => firstNegHit n j)
      (V := fun j => splitBefore n j ∩ shiftBy j ⁻¹' stripExitsBefore (n : ℝ)
        (axisSet {j | j ≤ 0}) 0) (measurableSet_stripExitsBefore _ _ _)
      (measurableSet_stripExitsBefore _ _ _)
      (fun j => (dependsOnFirst_firstNegHit n j).measurableSet)
      (fun j => (dependsOnFirst_splitBefore n j).measurableSet.inter
        (measurable_shiftBy j hEm))
      (stripExitsBefore_anti (B := axisSet {j | j ≤ 0}) (B' := axisSet Set.univ)
        (fun z hz => ⟨hz.1, trivial⟩) _ _)
      (Set.Subset.antisymm (diff_subset_iUnion hn)
        (Set.iUnion_subset fun j => splitBefore_inter_subset n j))
      (fun a b hab => ?_) (fun j => ?_) (fun a b hab => ?_) (disjoint_strip_firstNegHit n)
      (measure_compl_strip_union_eq_zero hn)
    · rcases lt_or_gt_of_ne hab with h | h
      · exact disjoint_pieces h
      · exact (disjoint_pieces h).symm
    · rw [markov_split (dependsOnFirst_splitBefore n j) hEm, ← revNeg_preimage_firstNegHit,
        (measurePreserving_revNeg j).measure_preimage
          (dependsOnFirst_firstNegHit n j).measurableSet.nullMeasurableSet]
    · rcases lt_or_gt_of_ne hab with h | h
      · exact disjoint_firstNegHit h
      · exact (disjoint_firstNegHit h).symm

end FiniteAvalanches.Walk.Beurling
