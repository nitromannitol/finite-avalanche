import FiniteAvalanches.Walk.BarlowMasson.Ratio
import FiniteAvalanches.Walk.BarlowMasson.LoopErasure

/-!
# The reentry estimate for loop-erased walk

Barlow and Masson (2011), Lemma 2.4. Let `K` contain every site at distance at least `ρ₂` from
the origin and no site at distance less than `ρ₁`, with `k² ≤ ρ₁ ≤ ρ₂ ≤ 4 ρ₁`. Run the simple
random walk from the origin until it first hits `K`, at time `T`, and loop-erase it. The
probability that the loop erasure, after its first site at distance at least `k`, visits the
disk of radius `r` is at most `C r / k`.

## Proof

If the erasure at time `T` is `α ++ q` with `α` ending at its first site `z` at distance at least
`k`, then `α` is the erasure at the last time `t` at which the walk is at `z`, the walk avoids
`α` after `t`, and the sites of `q` are visited after `t` (`exists_time_of_isPrefix`,
`isPrefix_walkErase_of_avoids`). So the event is contained in the union over the pairs `(α, t)`
of `{walkErase t = α, K not hit by time t}` followed, for the walk restarted at `z`, by the
event of reaching the disk of radius `r` before `α ∪ K` and then `K` before `α`. By the Markov
property at time `t` and the reentry ratio (`reentry_ratio_le`), each term is at most `C r / k`
times the probability of `{walkErase t = α, K not hit by time t}` followed by reaching `K` before
`α`. These last events are disjoint for different pairs `(α, t)`, so their probabilities sum to
at most one.

## Main statements

* `IsExitPrefix`: a loop-erased prefix from the origin whose last site is its first site at
  distance at least `k`.
* `reentry_le`: the reentry estimate.
-/

noncomputable section

namespace FiniteAvalanches.Walk.BarlowMasson

open LatticeProb MeasureTheory FiniteAvalanches.Walk.Beurling
open FiniteAvalanches.Wilson.Lattice

/-- A chain from the origin whose last site is its first site at distance at least `k`. -/
def IsExitPrefix (k : ℕ) (α : List (Site 2)) : Prop :=
  ∃ h : α ≠ [], α.head h = 0 ∧ α.IsChain (fun a b => euclidNorm (b - a) ≤ 1) ∧
    (∀ a ∈ α.dropLast, euclidNorm a < k) ∧ (k : ℝ) ≤ euclidNorm (α.getLast h)

/-- The reentry event: the loop erasure of the walk stopped at its first visit to `K`, after
its first site at distance at least `k`, visits the disk of radius `r`. -/
def reentry (K : Set (Site 2)) (k r : ℕ) : Set (ℕ → Dir 2) :=
  {ω | ∃ T, walkPos 0 ω T ∈ K ∧ (∀ s < T, walkPos 0 ω s ∉ K) ∧
    ∃ α q, walkErase 0 ω T = α ++ q ∧ IsExitPrefix k α ∧ ∃ v ∈ q, euclidNorm v < r}

theorem IsExitPrefix.norm_getLast_lt {k : ℕ} {α : List (Site 2)} (hα : IsExitPrefix k α)
    (hk : 0 < k) : euclidNorm (α.getLast hα.fst) < k + 1 := by
  obtain ⟨h, hhead, hchain, hdrop, hlast⟩ := hα
  have hd : α.dropLast ≠ [] := by
    rcases α with _ | ⟨a, l⟩
    · exact absurd rfl h
    · cases l with
      | nil =>
        exfalso
        simp only [List.head_cons, List.getLast_singleton] at hhead hlast
        rw [hhead, euclidNorm_zero] at hlast
        have : (0 : ℝ) < k := by exact_mod_cast hk
        linarith
      | cons b l => simp
  have hsplit := List.dropLast_append_getLast h
  have hrel : euclidNorm (α.getLast h - α.dropLast.getLast hd) ≤ 1 := by
    rw [← hsplit] at hchain
    have := hchain.rel_getLast_head_of_append hd (List.cons_ne_nil _ _)
    simpa using this
  have hp := hdrop _ (List.getLast_mem hd)
  have := euclidNorm_add_le (α.getLast h - α.dropLast.getLast hd) (α.dropLast.getLast hd)
  rw [sub_add_cancel] at this
  linarith

/-- The data of the reentry ratio for an exit prefix. -/
def reentryData (k : ℕ) (α : List (Site 2)) (hα : IsExitPrefix k α) (hk : 0 < k)
    (K : Set (Site 2)) (ρ₁ ρ₂ : ℝ) (hK1 : ∀ w, ρ₂ ≤ euclidNorm w → w ∈ K)
    (hK2 : ∀ w ∈ K, ρ₁ ≤ euclidNorm w) (hsq : (k : ℝ) ^ 2 ≤ ρ₁) (hρ : ρ₁ ≤ ρ₂)
    (hρ₂ : ρ₂ ≤ 4 * ρ₁) : ReentryData where
  k := k
  z := α.getLast hα.fst
  α := {a | a ∈ α}
  K := K
  ρ₁ := ρ₁
  ρ₂ := ρ₂
  z_mem := List.getLast_mem _
  le_norm_z := hα.snd.2.2.2
  norm_z_lt := hα.norm_getLast_lt hk
  norm_lt := fun a ha haz => hα.snd.2.2.1 a (List.mem_dropLast_of_mem_of_ne_getLast ha haz)
  len := α.length - 1
  path := fun i => α.getD i 0
  path_zero := by
    obtain ⟨h, hhead, -⟩ := hα
    rcases α with _ | ⟨a, l⟩
    · exact absurd rfl h
    · simpa using hhead
  path_len := by
    rw [List.getD_eq_getElem _ _ (by have := List.length_pos_of_ne_nil hα.fst; omega),
      List.getLast_eq_getElem]
  path_step := by
    intro i hi
    have hi' : i + 1 < α.length := by omega
    rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ (by omega)]
    exact List.isChain_iff_getElem.1 hα.snd.2.1 i hi'
  path_mem := by
    intro i hi
    have hlen := List.length_pos_of_ne_nil hα.fst
    show α.getD i 0 ∈ α
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  mem_K := hK1
  le_norm_K := hK2
  sq_le_ρ₁ := hsq
  ρ₁_le := hρ
  ρ₂_le := hρ₂

theorem measurableSet_firstStep {f : Site 2 → Set (ℕ → Dir 2)} (hf : ∀ y, MeasurableSet (f y))
    (z : Site 2) : MeasurableSet {ω : ℕ → Dir 2 | shiftBy 1 ω ∈ f (z + dirVec (ω 0))} := by
  have h : {ω : ℕ → Dir 2 | shiftBy 1 ω ∈ f (z + dirVec (ω 0))} =
      ⋃ a : Dir 2, {ω | ω 0 = a} ∩ shiftBy 1 ⁻¹' f (z + dirVec a) := by
    ext ω
    simp
  rw [h]
  exact MeasurableSet.iUnion fun a =>
    (show MeasurableSet {ω : ℕ → Dir 2 | ω 0 = a} from
      (measurableSet_singleton a).preimage (measurable_pi_apply 0)).inter
        (measurable_shiftBy 1 (hf _))

theorem walkErase_congr {x : Site 2} {ω ω' : ℕ → Dir 2} {t : ℕ} (h : ∀ i < t, ω i = ω' i) :
    ∀ T ≤ t, walkErase x ω T = walkErase x ω' T := by
  intro T hT
  induction T with
  | zero => rw [walkErase_zero', walkErase_zero']
  | succ T ih =>
    rw [walkErase_succ', walkErase_succ', ih (by omega), walkPos_congr_of_le x h hT]

theorem IsExitPrefix.eq_of_isPrefix {k : ℕ} {α α' : List (Site 2)} (hα : IsExitPrefix k α)
    (hα' : IsExitPrefix k α') (h : α <+: α') : α = α' := by
  obtain ⟨c, rfl⟩ := h
  by_cases hc : c = []
  · simp [hc]
  · exfalso
    obtain ⟨h0, -, -, -, hlast⟩ := hα
    obtain ⟨-, -, -, hdrop', -⟩ := hα'
    have hmem : α.getLast h0 ∈ (α ++ c).dropLast := by
      rw [List.dropLast_append_of_ne_nil hc]
      exact List.mem_append_left _ (List.getLast_mem h0)
    have := hdrop' _ hmem
    linarith

/-- The exit prefixes of scale `k`, indexed with a time. -/
abbrev ReentryIndex (k : ℕ) := {α : List (Site 2) // IsExitPrefix k α} × ℕ

/-- The last site of an exit prefix. -/
def ReentryIndex.z {k : ℕ} (i : ReentryIndex k) : Site 2 := i.1.1.getLast i.1.2.fst

/-- The set of sites of an exit prefix. -/
def ReentryIndex.set {k : ℕ} (i : ReentryIndex k) : Set (Site 2) := {a | a ∈ i.1.1}

/-- The erasure at time `t` is the prefix, and the walk has not visited `K` by time `t`. -/
def reentryHead (K : Set (Site 2)) {k : ℕ} (i : ReentryIndex k) : Set (ℕ → Dir 2) :=
  {ω | walkErase 0 ω i.2 = i.1.1 ∧ ∀ s ≤ i.2, walkPos 0 ω s ∉ K}

/-- From the last site of the prefix, the walk reaches the disk of radius `r` before the prefix and
`K`, and then `K` before the prefix, at positive times. -/
def reentryTail (K : Set (Site 2)) {k : ℕ} (r : ℕ) (i : ReentryIndex k) : Set (ℕ → Dir 2) :=
  {ω | shiftBy 1 ω ∈ reachesThen {w | euclidNorm w < r} (i.set ∪ K) K i.set (i.z + dirVec (ω 0))}

theorem dependsOnFirst_reentryHead (K : Set (Site 2)) {k : ℕ} (i : ReentryIndex k) :
    DependsOnFirst i.2 (reentryHead K i) := by
  intro ω ω' h
  simp only [reentryHead, Set.mem_setOf_eq]
  rw [walkErase_congr h i.2 le_rfl]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun s hs => by rw [← walkPos_congr_of_le 0 h hs]; exact h2 s hs⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun s hs => by rw [walkPos_congr_of_le 0 h hs]; exact h2 s hs⟩

theorem walkPos_shift_one (ω : ℕ → Dir 2) (t u : ℕ) :
    walkPos (walkPos 0 ω t + dirVec (shiftBy t ω 0)) (shiftBy 1 (shiftBy t ω)) u =
      walkPos 0 ω (t + 1 + u) := by
  rw [← walkPos_one_add, ← walkPos_add_shiftBy, add_assoc]

theorem walkPos_eq_z_of_head {k : ℕ} {i : ReentryIndex k} {ω : ℕ → Dir 2}
    (h : walkErase 0 ω i.2 = i.1.1) : walkPos 0 ω i.2 = i.z := by
  rw [← walkErase_getLast 0 ω i.2]
  simp only [ReentryIndex.z, h]

theorem reentry_subset (K : Set (Site 2)) (k r : ℕ) (hzK : ∀ i : ReentryIndex k, i.z ∉ K)
    (hvK : ∀ v, euclidNorm v < r → v ∉ K) :
    reentry K k r ⊆ ⋃ i : ReentryIndex k, reentryHead K i ∩ shiftBy i.2 ⁻¹' reentryTail K r i := by
  rintro ω ⟨T, hT, hfirst, α, q, hL, hα, v, hvq, hvr⟩
  have hpre : α <+: walkErase 0 ω T := ⟨q, hL.symm⟩
  obtain ⟨t, htT, ht, havoid⟩ := exists_time_of_isPrefix 0 ω hα.fst hpre
  set i : ReentryIndex k := (⟨α, hα⟩, t)
  have hzt : walkPos 0 ω t = i.z := walkPos_eq_z_of_head (i := i) ht
  have htT' : t < T := by
    rcases lt_or_eq_of_le htT with h | h
    · exact h
    · exact absurd (h ▸ hT) (hzt ▸ hzK i)
  obtain ⟨q', hq', hq'v⟩ := isPrefix_walkErase_of_avoids 0 ω htT (by rw [ht]; exact havoid)
  rw [ht, hL] at hq'
  have hqq : q = q' := List.append_cancel_left hq'
  obtain ⟨sv, hsv1, hsv2, hsv3⟩ := hq'v v (hqq ▸ hvq)
  refine Set.mem_iUnion.2 ⟨i, ⟨ht, fun s (hs : s ≤ t) => hfirst s (by omega)⟩, ?_⟩
  show shiftBy 1 (shiftBy t ω) ∈ reachesThen {w | euclidNorm w < r} (i.set ∪ K) K i.set
    (i.z + dirVec (shiftBy t ω 0))
  rw [← hzt]
  refine ⟨sv - t - 1, T - t - 1, by omega, ?_, fun s hs => ?_, ?_, fun s hs1 hs2 => ?_⟩
  · rw [walkPos_shift_one, show t + 1 + (sv - t - 1) = sv by omega, hsv3]
    exact hvr
  · rw [walkPos_shift_one]
    rintro (h | h)
    · exact havoid (t + 1 + s) (by omega) (by omega) h
    · rcases lt_or_eq_of_le (show t + 1 + s ≤ T by omega) with hlt | heq
      · exact hfirst _ hlt h
      · rw [heq, show T = sv by omega, hsv3] at h
        exact hvK v hvr h
  · rw [walkPos_shift_one, show t + 1 + (T - t - 1) = T by omega]
    exact hT
  · rw [walkPos_shift_one]
    exact havoid (t + 1 + s) (by omega) (by omega)

theorem reentry_disjoint_aux (K : Set (Site 2)) {k : ℕ} (i j : ReentryIndex k) (ω : ℕ → Dir 2)
    (hij : i.2 ≤ j.2) (hi : ω ∈ reentryHead K i ∩ shiftBy i.2 ⁻¹' reachesAfter K i.set i.z)
    (hj : ω ∈ reentryHead K j ∩ shiftBy j.2 ⁻¹' reachesAfter K j.set j.z) : i = j := by
  obtain ⟨⟨hA1, -⟩, hD⟩ := hi
  obtain ⟨⟨hA1', hA2'⟩, -⟩ := hj
  have hzt : walkPos 0 ω i.2 = i.z := walkPos_eq_z_of_head hA1
  obtain ⟨u, hu1, hu2⟩ := hD
  rw [← hzt, walkPos_shift_one] at hu1
  have hu2' : ∀ s ≤ u, walkPos 0 ω (i.2 + 1 + s) ∉ i.set := by
    intro s hs
    have := hu2 s hs
    rwa [← hzt, walkPos_shift_one] at this
  have ht'u : j.2 ≤ i.2 + u := by
    by_contra hlt
    exact hA2' (i.2 + 1 + u) (by omega) hu1
  have havoid : ∀ s, i.2 < s → s ≤ j.2 → walkPos 0 ω s ∉ walkErase 0 ω i.2 := by
    intro s hs1 hs2
    rw [hA1]
    have := hu2' (s - i.2 - 1) (by omega)
    rwa [show i.2 + 1 + (s - i.2 - 1) = s by omega] at this
  obtain ⟨q, hq, -⟩ := isPrefix_walkErase_of_avoids 0 ω hij havoid
  rw [hA1, hA1'] at hq
  have hαα : i.1.1 = j.1.1 := i.1.2.eq_of_isPrefix j.1.2 ⟨q, hq.symm⟩
  have h1 : i.1 = j.1 := Subtype.ext hαα
  have htt : i.2 = j.2 := by
    by_contra hne
    have hlt : i.2 < j.2 := lt_of_le_of_ne hij hne
    have hzt' : walkPos 0 ω j.2 = j.z := walkPos_eq_z_of_head hA1'
    refine havoid j.2 hlt le_rfl ?_
    rw [hA1, hzt']
    simp only [ReentryIndex.z, ← h1]
    exact List.getLast_mem _
  exact Prod.ext h1 htt

/-- **The reentry estimate** (Barlow and Masson (2011), Lemma 2.4). -/
theorem reentry_le : ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ r₀ : ℕ, ∀ (K : Set (Site 2)) (ρ₁ ρ₂ : ℝ),
    (∀ w, ρ₂ ≤ euclidNorm w → w ∈ K) → (∀ w ∈ K, ρ₁ ≤ euclidNorm w) →
    ∀ k r : ℕ, k₀ ≤ k → r₀ ≤ r → 64 * r ≤ k → (k : ℝ) ^ 2 ≤ ρ₁ → ρ₁ ≤ ρ₂ → ρ₂ ≤ 4 * ρ₁ →
      prob (reentry K k r) ≤ C * ((r : ℝ) / k) := by
  obtain ⟨Cr, hCr, kr, rr, hratio⟩ := reentry_ratio_le
  refine ⟨Cr, hCr, max kr 2, rr, fun K ρ₁ ρ₂ hK1 hK2 k r hk hr hrk hsq hρ hρ₂ => ?_⟩
  have hkr : kr ≤ k := le_of_max_le_left hk
  have hk2 : 2 ≤ k := le_of_max_le_right hk
  have hk0 : 0 < k := by omega
  have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  set ε : ℝ := Cr * ((r : ℝ) / k) with hε
  have hε0 : 0 ≤ ε := by positivity
  have hzK : ∀ i : ReentryIndex k, i.z ∉ K := by
    intro i hzK'
    have h1 := i.1.2.norm_getLast_lt hk0
    have h2 := hK2 _ hzK'
    have : (k : ℝ) + 1 < k ^ 2 := by nlinarith
    exact absurd h2 (not_le.2 (by simp only [ReentryIndex.z] at h1 ⊢; linarith))
  have hvK : ∀ v, euclidNorm v < r → v ∉ K := by
    intro v hv hvK'
    have := hK2 v hvK'
    have hrk' : (r : ℝ) ≤ k := by
      have : ((64 * r : ℕ) : ℝ) ≤ k := by exact_mod_cast hrk
      push_cast at this
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      linarith
    nlinarith
  have hCm : ∀ i : ReentryIndex k, MeasurableSet (reentryTail K r i) := fun i =>
    measurableSet_firstStep (f := reachesThen {w | euclidNorm w < r} (i.set ∪ K) K i.set)
      (fun _ => measurableSet_reachesThen _ _ _ _ _) i.z
  have hDm : ∀ i : ReentryIndex k, MeasurableSet (reachesAfter K i.set i.z) := fun i =>
    measurableSet_firstStep (f := reaches K i.set) (fun _ => measurableSet_reaches _ _ _) i.z
  have hterm : ∀ i : ReentryIndex k, pathLaw 2 (reentryTail K r i) ≤
      ENNReal.ofReal ε * pathLaw 2 (reachesAfter K i.set i.z) := by
    intro i
    have h := hratio (reentryData k i.1.1 i.1.2 hk0 K ρ₁ ρ₂ hK1 hK2 hsq hρ hρ₂) hkr r hr hrk
    change prob (reentryTail K r i) ≤ ε * prob (reachesAfter K i.set i.z) at h
    rw [← ENNReal.ofReal_toReal (measure_ne_top (pathLaw 2) (reentryTail K r i)),
      ← ENNReal.ofReal_toReal (measure_ne_top (pathLaw 2) (reachesAfter K i.set i.z)),
      ← ENNReal.ofReal_mul hε0]
    exact ENNReal.ofReal_le_ofReal h
  have hdisj : Pairwise (Function.onFun Disjoint fun i : ReentryIndex k =>
      reentryHead K i ∩ shiftBy i.2 ⁻¹' reachesAfter K i.set i.z) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro ω hi hj
    rcases le_total i.2 j.2 with h | h
    · exact hij (reentry_disjoint_aux K i j ω h hi hj)
    · exact hij (reentry_disjoint_aux K j i ω h hj hi).symm
  have hmain : pathLaw 2 (reentry K k r) ≤ ENNReal.ofReal ε := by
    calc pathLaw 2 (reentry K k r) ≤ pathLaw 2 (⋃ i : ReentryIndex k,
          reentryHead K i ∩ shiftBy i.2 ⁻¹' reentryTail K r i) :=
          measure_mono (reentry_subset K k r hzK hvK)
      _ ≤ ∑' i : ReentryIndex k, pathLaw 2 (reentryHead K i ∩ shiftBy i.2 ⁻¹' reentryTail K r i) :=
          measure_iUnion_le _
      _ = ∑' i : ReentryIndex k, pathLaw 2 (reentryHead K i) * pathLaw 2 (reentryTail K r i) :=
          tsum_congr fun i => markov_split (dependsOnFirst_reentryHead K i) (hCm i)
      _ ≤ ∑' i : ReentryIndex k, pathLaw 2 (reentryHead K i) *
          (ENNReal.ofReal ε * pathLaw 2 (reachesAfter K i.set i.z)) :=
          ENNReal.tsum_le_tsum fun i => mul_le_mul_right (hterm i) _
      _ = ENNReal.ofReal ε * ∑' i : ReentryIndex k,
          pathLaw 2 (reentryHead K i ∩ shiftBy i.2 ⁻¹' reachesAfter K i.set i.z) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun i => ?_
          rw [markov_split (dependsOnFirst_reentryHead K i) (hDm i)]
          ring
      _ = ENNReal.ofReal ε * pathLaw 2 (⋃ i : ReentryIndex k,
          reentryHead K i ∩ shiftBy i.2 ⁻¹' reachesAfter K i.set i.z) := by
          rw [measure_iUnion hdisj fun i =>
            (dependsOnFirst_reentryHead K i).measurableSet.inter (measurable_shiftBy i.2 (hDm i))]
      _ ≤ ENNReal.ofReal ε * 1 := mul_le_mul_right MeasureTheory.prob_le_one _
      _ = ENNReal.ofReal ε := mul_one _
  exact ENNReal.toReal_le_of_le_ofReal hε0 hmain

end FiniteAvalanches.Walk.BarlowMasson

