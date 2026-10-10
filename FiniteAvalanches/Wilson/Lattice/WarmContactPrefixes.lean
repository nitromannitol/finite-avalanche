import FiniteAvalanches.Wilson.Lattice.CofiniteHistorySuccess
import FiniteAvalanches.Wilson.Lattice.QueryPrefixes
import FiniteAvalanches.Wilson.Lattice.LocalizationUnion
import FiniteAvalanches.Wilson.Lattice.GlobalContactPersistence

/-! Actual histories after a nonempty warm-up query batch. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.WarmContactPrefixes
open LatticeProb FiniteAvalanches Sandpile MeasureTheory
open BatchRestart ConditionalIteration7 ActualContactHistory ActualContactRestriction
open ActualQueryPrefixes ActualLocalizationUnion GlobalContactPersistence
open scoped Classical
noncomputable section

/-- The complete first box has already been queried at iteration index zero. -/
def warmPrefix (Q : ℕ → List (Site 2)) (i : ℕ) : List (Site 2) :=
  queryPrefix Q (i + 1)

/-- Failures at indices one through n; the warm-up is retained in every history. -/
def warmSurviving (R : RootPair) (Q : ℕ → List (Site 2))
    (F : ℕ → Finset (Site 2)) (h : ℕ → ℕ) (t : ℝ) : ℕ → Set Rows
  | 0 => Set.univ
  | i + 1 => (warmSurviving R Q F h t i ∩ localizedPrefix R (warmPrefix Q i) (h i)) \
      continuationContactEvent (initialSampler R) (warmPrefix Q (i + 1)) (F i) t

theorem measurable_warmSurviving_consumed (R : RootPair) (Q : ℕ → List (Site 2))
    (F : ℕ → Finset (Site 2)) (h : ℕ → ℕ) (t : ℝ) (i : ℕ) :
    MeasurableSet[consumedRows (warmPrefix Q i).length] (warmSurviving R Q F h t i) := by
  induction i with
  | zero => exact MeasurableSet.univ
  | succ i ih =>
    have hm := consumedRows_mono (queryPrefix_length_mono Q (Nat.le_succ (i + 1)))
    exact (hm _ (ih.inter (measurable_localizedPrefix_consumed R _ _))).diff
      (measurable_contact_success_consumed R _ _ _)

theorem mem_warmSurviving_iff (R : RootPair) (Q : ℕ → List (Site 2))
    (F : ℕ → Finset (Site 2)) (h : ℕ → ℕ) (t : ℝ) (n : ℕ) (ξ : Rows) :
    ξ ∈ warmSurviving R Q F h t n ↔ ∀ i < n,
      ξ ∈ localizedPrefix R (warmPrefix Q i) (h i) ∧
      ξ ∉ continuationContactEvent (initialSampler R) (warmPrefix Q (i + 1)) (F i) t := by
  induction n with
  | zero => simp only [warmSurviving, Set.mem_univ, Nat.not_lt_zero,
      IsEmpty.forall_iff, implies_true]
  | succ n ih =>
    change (ξ ∈ warmSurviving R Q F h t n ∧
      ξ ∈ localizedPrefix R (warmPrefix Q n) (h n)) ∧ _ ↔ _
    rw [ih]
    constructor
    · rintro ⟨⟨hp, hl⟩, hf⟩ i hi
      by_cases hin : i < n
      · exact hp i hin
      · have he : i = n := by omega
        subst i
        exact ⟨hl, hf⟩
    · intro hp
      exact ⟨⟨fun i hi => hp i (Nat.lt_trans hi (Nat.lt_succ_self n)),
        (hp n (Nat.lt_succ_self n)).1⟩, (hp n (Nat.lt_succ_self n)).2⟩

/-- Restrict an actual one-step atom inequality to any consumed-row event.
Both the whole atom and its restriction use the same fresh tail rows. -/
theorem restricted_atom_success (R : RootPair) (L Q : List (Site 2))
    (out : SamplerState) (E : Set Rows) (hE : MeasurableSet[consumedRows L.length] E)
    (F : Finset (Site 2)) (t p : ℝ)
    (hsuccess : p * wilsonRows.real (historyAtom R L out) ≤
      wilsonRows.real (historyAtom R L out ∩
        continuationContactEvent (initialSampler R) (L ++ Q) F t)) :
    p * wilsonRows.real (E ∩ historyAtom R L out) ≤
      wilsonRows.real ((E ∩ historyAtom R L out) ∩
        continuationContactEvent (initialSampler R) (L ++ Q) F t) := by
  let H := historyAtom R L out
  let S := continuationContactEvent (initialSampler R) (L ++ Q) F t
  let T := (fun ξ : Rows => fun j => ξ (j + L.length)) ⁻¹'
    continuationContactEvent out Q F t
  have hTf : MeasurableSet[freshRows L.length] T :=
    (measurable_continuationContactEvent out Q F t).preimage (measurable_tail_fresh L.length)
  have he : H ∩ S = H ∩ T := by
    ext ξ
    constructor
    · rintro ⟨hξ, next, hn, σ, hσ, hc⟩
      rw [samplerRun_append, hξ, Option.bind_some] at hn
      exact ⟨hξ, next, hn, σ, hσ, hc⟩
    · rintro ⟨hξ, next, hn, σ, hσ, hc⟩
      refine ⟨hξ, next, ?_, σ, hσ, hc⟩
      rw [samplerRun_append, hξ, Option.bind_some]
      exact hn
  have hHc : MeasurableSet[consumedRows L.length] H := measurable_historyAtom_consumed R L out
  have hAc := hE.inter hHc
  have hfactor (A : Set Rows) (hA : MeasurableSet[consumedRows L.length] A) :
      wilsonRows.real (A ∩ T) = wilsonRows.real A * wilsonRows.real T := by
    have hi := (freshRows_indep_consumed L.length).symm.indepSet_of_measurableSet hA hTf
    exact congrArg ENNReal.toReal hi.measure_inter_eq_mul |>.trans ENNReal.toReal_mul
  have hs : p * wilsonRows.real H ≤ wilsonRows.real H * wilsonRows.real T := by
    change p * wilsonRows.real H ≤ wilsonRows.real (H ∩ S) at hsuccess
    rw [he, hfactor H hHc] at hsuccess
    exact hsuccess
  have heA : (E ∩ H) ∩ S = (E ∩ H) ∩ T := by
    rw [Set.inter_assoc, he, ← Set.inter_assoc]
  change p * wilsonRows.real (E ∩ H) ≤ wilsonRows.real ((E ∩ H) ∩ S)
  rw [heA, hfactor (E ∩ H) hAc]
  by_cases hz : wilsonRows.real H = 0
  · have hAz : wilsonRows.real (E ∩ H) = 0 := le_antisymm
      ((measureReal_mono Set.inter_subset_right).trans hz.le) measureReal_nonneg
    rw [hAz, mul_zero, zero_mul]
  · have hp : p ≤ wilsonRows.real T :=
      (mul_le_mul_iff_right₀ (lt_of_le_of_ne measureReal_nonneg (Ne.symm hz))).mp
        (by simpa only [mul_comm] using hs)
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hp
      (measureReal_nonneg (μ := wilsonRows) (s := E ∩ H))

/-- Proved null nontermination is the only discarded event. -/
theorem warm_failures_le_surviving_add_exits (R : RootPair)
    (Q : ℕ → List (Site 2)) (F : ℕ → Finset (Site 2)) (h : ℕ → ℕ) (t : ℝ) (n : ℕ) :
    wilsonRows.real {ξ : Rows | ∀ i < n,
      ξ ∉ continuationContactEvent (initialSampler R) (warmPrefix Q (i + 1)) (F i) t} ≤
      wilsonRows.real (warmSurviving R Q F h t n) +
        ∑ i : Fin n, wilsonRows.real (prefixExit R (warmPrefix Q i.val) (h i.val)) := by
  let A := {ξ : Rows | ∀ i < n,
    ξ ∉ continuationContactEvent (initialSampler R) (warmPrefix Q (i + 1)) (F i) t}
  let B := warmSurviving R Q F h t n
  let E := fun i : Fin n => prefixExit R (warmPrefix Q i.val) (h i.val)
  have hs : ∀ᵐ ξ ∂wilsonRows, ∀ i : Fin n,
      ∃ out, samplerRun (initialSampler R) (warmPrefix Q i.val) ξ = some out :=
    ae_all_iff.mpr (fun i => wilson_sampler_success_conull R (warmPrefix Q i.val))
  have hsub : ∀ᵐ ξ ∂wilsonRows, ξ ∈ A → ξ ∈ B ∪ ⋃ i : Fin n, E i := by
    filter_upwards [hs] with ξ hξ ha
    by_cases hb : ξ ∈ B
    · exact Or.inl hb
    · apply Or.inr
      by_contra he
      apply hb
      apply (mem_warmSurviving_iff R Q F h t n ξ).mpr
      intro i hi
      refine ⟨?_, ha i hi⟩
      obtain ⟨out, hout⟩ := hξ ⟨i, hi⟩
      refine ⟨out, hout, ?_⟩
      intro p hp j
      by_contra hj
      apply he
      refine Set.mem_iUnion.mpr ⟨⟨i, hi⟩, out, hout, p, hp, j, ?_⟩
      exact Nat.lt_of_not_ge (fun hr => hj ((site_radius_zero_le_iff _ _).mp hr))
  calc
    _ ≤ wilsonRows.real (B ∪ ⋃ i : Fin n, E i) :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    _ ≤ wilsonRows.real B + wilsonRows.real (⋃ i : Fin n, E i) := measureReal_union_le _ _
    _ ≤ _ := add_le_add le_rfl (measureReal_iUnion_fintype_le (μ := wilsonRows) E)

/-- Transfer the actual global law after including the warm-up in every prefix. -/
theorem global_low_mass_le_warm_failures (R : RootPair) (K : Finset (Site 2))
    (Q : ℕ → List (Site 2)) (F : ℕ → Finset (Site 2)) (n : ℕ) (t : ℝ)
    (hF : ∀ i < n, F i ⊆ K) :
    (wilsonColorLaw R).real {σ : ColorField | (contacts K σ : ℝ) < t} ≤
      wilsonRows.real {ξ : Rows | ∀ i < n,
        ξ ∉ continuationContactEvent (initialSampler R) (warmPrefix Q (i + 1)) (F i) t} := by
  let G := fun i => if i = 0 then ∅ else F (i - 1)
  have hg : ∀ i < n + 1, G i ⊆ K := by
    intro i hi
    dsimp only [G]
    split_ifs with hz
    · exact Finset.empty_subset K
    · exact hF (i - 1) (by omega)
  have hb := global_low_mass_le_all_failures R K Q G (n + 1) t hg
  apply hb.trans
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro ξ hξ i hi
  have h := hξ (i + 1) (by omega)
  simpa only [G, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
    Nat.add_sub_cancel, warmPrefix] using h

end
end FiniteAvalanches.Wilson.Lattice.WarmContactPrefixes
