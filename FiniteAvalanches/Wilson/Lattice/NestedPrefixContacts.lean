import FiniteAvalanches.Probability.Multiscale.ScaleExponent
import FiniteAvalanches.Wilson.Lattice.ColorMarginal
import FiniteAvalanches.Wilson.Lattice.ContactHistory
import FiniteAvalanches.Sandpile.LocalConfinement

/-! Incoming cd552a5, main.tex 511: consecutive query boxes starting at scale 1.
The actual sampler output is partial and a failed run remains `none`.
The finite contact-law identity uses the registered Wilson law only through its
finite joint-color characterization. No confinement or recurrence is assumed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.CurrentNestedPrefix
open LatticeProb FiniteAvalanches Sandpile MeasureTheory
open Probability.CurrentScale BatchRestart ConditionalIteration7 ActualContactHistory
open scoped Classical
noncomputable section

/-- The complete query box at the literal current scale. -/
def stageBox (b i : ℕ) : Finset (Site 2) := boxSites (3 * scale b i + 1)

/-- Stage zero is auxiliary. Each positive stage appends only newly requested sites. -/
def stagePrefix (b : ℕ) : ℕ → List (Site 2)
  | 0 => []
  | i + 1 => stagePrefix b i ++ (stageBox b (i + 1) \ (stagePrefix b i).toFinset).toList

/-- The literal finite window of source origins at stage i. -/
def sourceWindow (K : Finset (Site 2)) (b i : ℕ) : Finset (Site 2) :=
  K.filter (fun x => siteRadius 0 x ≤ 3 * scale b i)

theorem sourceWindow_eq_real_filter (K : Finset (Site 2)) (b i : ℕ) :
    sourceWindow K b i =
      K.filter (fun x => (siteRadius 0 x : ℝ) ≤ 3 * (scale b i : ℝ)) := by
  ext x
  simp only [sourceWindow, Finset.mem_filter]
  constructor
  · rintro ⟨hx, hr⟩
    exact ⟨hx, by exact_mod_cast hr⟩
  · rintro ⟨hx, hr⟩
    exact ⟨hx, by exact_mod_cast hr⟩

theorem scale_mono (b : ℕ) (hb : 6 ≤ b) : Monotone (scale b) := by
  intro i j hij
  exact Nat.pow_le_pow_right (by decide : 0 < 2)
    (Nat.pow_le_pow_right (by omega : 0 < b) hij)

theorem stageBox_mono (b : ℕ) (hb : 6 ≤ b) {i j : ℕ} (hij : i ≤ j) :
    stageBox b i ⊆ stageBox b j := by
  apply box_sites_mono
  have h := scale_mono b hb hij
  omega

theorem prefix_zero (b : ℕ) : stagePrefix b 0 = [] := rfl

theorem prefix_one (b : ℕ) : stagePrefix b 1 = (stageBox b 1).toList := by
  simp only [stagePrefix, List.toFinset_nil, Finset.sdiff_empty, List.nil_append]

theorem prefix_succ (b i : ℕ) :
    stagePrefix b (i + 1) = stagePrefix b i ++
      (stageBox b (i + 1) \ (stagePrefix b i).toFinset).toList := rfl

theorem prefix_nodup (b i : ℕ) : (stagePrefix b i).Nodup := by
  induction i with
  | zero => exact List.nodup_nil
  | succ i ih =>
    apply List.nodup_append.mpr
    refine ⟨ih, Finset.nodup_toList _, ?_⟩
    intro x hx y hy he
    subst y
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hy)).2
      (List.mem_toFinset.mpr hx)

theorem new_stage_mem_iff (b i : ℕ) (x : Site 2) :
    x ∈ (stageBox b (i + 1) \ (stagePrefix b i).toFinset).toList ↔
      x ∈ stageBox b (i + 1) ∧ x ∉ stagePrefix b i := by
  simp only [Finset.mem_toList, Finset.mem_sdiff, List.mem_toFinset]

theorem prefix_subset_stage (b : ℕ) (hb : 6 ≤ b) (i : ℕ) :
    ∀ x ∈ stagePrefix b i, x ∈ stageBox b i := by
  induction i with
  | zero => simp only [stagePrefix, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | succ i ih =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact stageBox_mono b hb (Nat.le_succ i) (ih x hx)
    · exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hx)).1

theorem prefix_mem_iff (b : ℕ) (hb : 6 ≤ b) (i : ℕ) (hi : 1 ≤ i) (x : Site 2) :
    x ∈ stagePrefix b i ↔ x ∈ stageBox b i := by
  cases i with
  | zero => omega
  | succ i =>
    constructor
    · exact prefix_subset_stage b hb (i + 1) x
    · intro hx
      change x ∈ stagePrefix b i ++ _
      by_cases hp : x ∈ stagePrefix b i
      · exact List.mem_append_left _ hp
      · exact List.mem_append_right _ (Finset.mem_toList.mpr
          (Finset.mem_sdiff.mpr ⟨hx, by simpa only [List.mem_toFinset] using hp⟩))

theorem prefix_toFinset (b : ℕ) (hb : 6 ≤ b) (i : ℕ) (hi : 1 ≤ i) :
    (stagePrefix b i).toFinset = stageBox b i := by
  ext x
  rw [List.mem_toFinset, prefix_mem_iff b hb i hi]

theorem prefix_exists_suffix (b : ℕ) {i j : ℕ} (hij : i ≤ j) :
    ∃ Q, stagePrefix b j = stagePrefix b i ++ Q := by
  induction j generalizing i with
  | zero =>
    have hi : i = 0 := Nat.eq_zero_of_le_zero hij
    subst i
    exact ⟨[], rfl⟩
  | succ j ih =>
    by_cases hi : i = j + 1
    · subst i
      exact ⟨[], (List.append_nil _).symm⟩
    · obtain ⟨Q, hQ⟩ := ih (show i ≤ j by omega)
      refine ⟨Q ++ (stageBox b (j + 1) \ (stagePrefix b j).toFinset).toList, ?_⟩
      rw [prefix_succ, hQ, List.append_assoc]

theorem prefix_covers_lattice (b : ℕ) (hb : 6 ≤ b) (x : Site 2) :
    ∃ i, 1 ≤ i ∧ x ∈ stagePrefix b i := by
  let i := siteRadius 0 x + 1
  have hi : 1 ≤ i := by omega
  have hpow : i ≤ b ^ i := (Nat.lt_pow_self (by omega : 1 < b)).le
  have hs : i ≤ scale b i := hpow.trans (Nat.lt_two_pow_self.le)
  refine ⟨i, hi, (prefix_mem_iff b hb i hi x).mpr ?_⟩
  apply (mem_box_sites _ _).mpr
  intro j
  have hj := (siteRadius_le_iff 0 x (3 * scale b i + 1)).mp
    (show siteRadius 0 x ≤ 3 * scale b i + 1 by omega) j
  simpa only [Pi.zero_apply, sub_zero, abs_le] using hj

theorem source_and_contact_subset_stage (K : Finset (Site 2)) (b i : ℕ) :
    sourceWindow K b i ∪ contactSites (sourceWindow K b i) ⊆ stageBox b i := by
  intro y hy
  have horigin {x : Site 2} (hx : x ∈ sourceWindow K b i) :
      x ∈ boxSites (3 * scale b i) := by
    apply (mem_box_sites _ _).mpr
    intro j
    have hj := (siteRadius_le_iff 0 x (3 * scale b i)).mp
      (Finset.mem_filter.mp hx).2 j
    simpa only [Pi.zero_apply, sub_zero, abs_le] using hj
  rcases Finset.mem_union.mp hy with hy | hy
  · exact box_sites_mono (Nat.le_succ _) (horigin hy)
  · obtain ⟨x, hx, hy⟩ := Finset.mem_biUnion.mp hy
    simp only [nbrFinset, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton] at hy
    obtain ⟨j, rfl | rfl⟩ := hy
    · exact box_sites_add_unit (horigin hx) j
    · exact box_sites_sub_unit (horigin hx) j

theorem source_and_contact_queried (K : Finset (Site 2)) (b : ℕ) (hb : 6 ≤ b)
    (i : ℕ) (hi : 1 ≤ i) :
    ∀ x ∈ sourceWindow K b i ∪ contactSites (sourceWindow K b i), x ∈ stagePrefix b i :=
  fun x hx => (prefix_mem_iff b hb i hi x).mpr
    (source_and_contact_subset_stage K b i hx)

/-- A genuine successful step knows its requested start, including a time-zero hit. -/
theorem samplerStep_covers_query (st out : SamplerState) (x : Site 2) (w : WalkDriver)
    (hs : samplerStep st x w = some out) : x ∈ out.covered := by
  by_cases hx : x ∈ st.covered
  · change out.colors x ≠ none
    rw [samplerStep_preserves_covered_colors st out x w hs x hx]
    exact hx
  · cases hT : hitTime st.covered x w with
    | none => simp [samplerStep, hx, hT] at hs
    | some T =>
      have hhit : position x w T ∈ st.covered :=
        ((hitTime_eq_some_iff _ _ _ _).mp hT).1
      have hne : x ≠ position x w T := fun he => hx (he.symm ▸ hhit)
      have hstart := walkErase_start_mem_dropLast x w T hne
      have he := Option.some.inj
        (by simpa only [samplerStep, if_neg hx, hT] using hs)
      rw [← he]
      change (if x ∈ (walkErase x w T).dropLast then
        st.colors (position x w T) else st.colors x) ≠ none
      rw [if_pos hstart]
      exact hhit

/-- Every requested site is actually known after a successful complete finite run. -/
theorem samplerRun_covers_queries (st out : SamplerState) (L : List (Site 2)) (ξ : Rows)
    (hs : samplerRun st L ξ = some out) : ∀ x ∈ L, x ∈ out.covered := by
  induction L generalizing st ξ with
  | nil => simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | cons x xs ih =>
    cases hh : samplerStep st x (ξ 0) with
    | none => simp [samplerRun, hh] at hs
    | some mid =>
      have ht : samplerRun mid xs (fun j => ξ (j + 1)) = some out := by
        simpa only [samplerRun, hh, Option.bind_some] using hs
      intro v hv
      rcases List.mem_cons.mp hv with hv | hv
      · subst v
        have hx := samplerStep_covers_query st mid x (ξ 0) hh
        change out.colors x ≠ none
        rw [samplerRun_preserves_covered_colors mid out xs _ ht x hx]
        exact hx
      · exact ih mid (fun j => ξ (j + 1)) ht v hv

theorem completed_prefix_contact_known (R : RootPair) (K : Finset (Site 2))
    (b : ℕ) (hb : 6 ≤ b) (i : ℕ) (hi : 1 ≤ i) (ξ : Rows) (out : SamplerState)
    (hs : samplerRun (initialSampler R) (stagePrefix b i) ξ = some out) :
    ∀ x ∈ sourceWindow K b i ∪ contactSites (sourceWindow K b i),
      ∃ c : Bool, out.colors x = some c := by
  intro x hx
  have hc := samplerRun_covers_queries _ out _ ξ hs x
    (source_and_contact_queried K b hb i hi x hx)
  cases he : out.colors x with
  | none => exact (hc he).elim
  | some c => exact ⟨c, rfl⟩

/-- The later genuine run factors through the earlier complete state and preserves known colors. -/
theorem completed_nested_prefix (R : RootPair) (b : ℕ) {i j : ℕ} (hij : i ≤ j)
    (ξ : Rows) (out : SamplerState)
    (hs : samplerRun (initialSampler R) (stagePrefix b j) ξ = some out) :
    ∃ (Q : List (Site 2)) (mid : SamplerState),
      stagePrefix b j = stagePrefix b i ++ Q ∧
      samplerRun (initialSampler R) (stagePrefix b i) ξ = some mid ∧
      samplerRun mid Q (fun k => ξ (k + (stagePrefix b i).length)) = some out ∧
      ∀ x ∈ mid.covered, out.colors x = mid.colors x := by
  obtain ⟨Q, hQ⟩ := prefix_exists_suffix b hij
  rw [hQ, samplerRun_append] at hs
  cases hm : samplerRun (initialSampler R) (stagePrefix b i) ξ with
  | none => simp only [hm, Option.bind_none] at hs; cases hs
  | some mid =>
    have ht : samplerRun mid Q (fun k => ξ (k + (stagePrefix b i).length)) = some out := by
      simpa only [hm, Option.bind_some] using hs
    exact ⟨Q, mid, hQ, rfl, ht,
      fun x hx => samplerRun_preserves_covered_colors mid out Q _ ht x hx⟩

/-- Agreement with one actual partial output fixes all original-incidence contacts. -/
theorem contacts_eq_on_completed_output (out : SamplerState) (F : Finset (Site 2))
    (σ τ : ColorField)
    (hσ : ∀ d ∈ contactSites F, out.colors d = some (σ d))
    (hτ : ∀ d ∈ contactSites F, out.colors d = some (τ d)) :
    contacts F σ = contacts F τ :=
  contacts_of_agree F (fun d hd => Option.some.inj ((hσ d hd).symm.trans (hτ d hd)))

/-- An arbitrary exterior extension exists, with no assertion that it is a sampled forest. -/
theorem completed_prefix_extension (R : RootPair) (K : Finset (Site 2))
    (b : ℕ) (hb : 6 ≤ b) (i : ℕ) (hi : 1 ≤ i) (ξ : Rows) (out : SamplerState)
    (hs : samplerRun (initialSampler R) (stagePrefix b i) ξ = some out) (σ₀ : ColorField) :
    ∃ σ : ColorField,
      (∀ d ∈ contactSites (sourceWindow K b i), out.colors d = some (σ d)) ∧
      ∀ d ∉ contactSites (sourceWindow K b i), σ d = σ₀ d := by
  have hknown : ∀ d ∈ contactSites (sourceWindow K b i), ∃ c, out.colors d = some c :=
    fun d hd => completed_prefix_contact_known R K b hb i hi ξ out hs d
      (Finset.mem_union.mpr (Or.inr hd))
  let σ : ColorField := fun d => if hd : d ∈ contactSites (sourceWindow K b i) then
    Classical.choose (hknown d hd) else σ₀ d
  refine ⟨σ, ?_, ?_⟩
  · intro d hd
    simp only [σ, dif_pos hd]
    exact Classical.choose_spec (hknown d hd)
  · intro d hd
    exact dif_neg hd

theorem contact_event_on_completed_fiber (R : RootPair) (L : List (Site 2))
    (F : Finset (Site 2)) (t : ℝ) (ξ : Rows) (out : SamplerState)
    (hs : samplerRun (initialSampler R) L ξ = some out) (σ : ColorField)
    (hσ : ∀ d ∈ contactSites F, out.colors d = some (σ d)) :
    ξ ∈ continuationContactEvent (initialSampler R) L F t ↔
      t ≤ (contacts F σ : ℝ) := by
  constructor
  · rintro ⟨next, hn, τ, hτ, hc⟩
    have he : next = out := Option.some.inj (hn.symm.trans hs)
    subst next
    change t ≤ (contacts F τ : ℝ) at hτ
    rw [contacts_eq_on_completed_output out F τ σ hc hσ] at hτ
    exact hτ
  · intro ht
    exact ⟨out, hs, σ, ht, hσ⟩

theorem contact_event_constant_on_fiber (R : RootPair) (L : List (Site 2))
    (F : Finset (Site 2)) (t : ℝ) (ξ η : Rows) (out : SamplerState)
    (hξ : samplerRun (initialSampler R) L ξ = some out)
    (hη : samplerRun (initialSampler R) L η = some out) :
    ξ ∈ continuationContactEvent (initialSampler R) L F t ↔
      η ∈ continuationContactEvent (initialSampler R) L F t := by
  constructor
  · rintro ⟨next, hn, σ, hσ, hc⟩
    have he : next = out := Option.some.inj (hn.symm.trans hξ)
    subst next
    exact ⟨out, hη, σ, hσ, hc⟩
  · rintro ⟨next, hn, σ, hσ, hc⟩
    have he : next = out := Option.some.inj (hn.symm.trans hη)
    subst next
    exact ⟨out, hξ, σ, hσ, hc⟩

/-- The complete output sigma algebra sees the literal contact event. -/
theorem measurable_contact_fullHistory (R : RootPair) (L : List (Site 2))
    (F : Finset (Site 2)) (t : ℝ) :
    MeasurableSet[fullHistory R L] (continuationContactEvent (initialSampler R) L F t) :=
  measurable_completed_observation R L
    (fun out => ∃ σ ∈ contactEvent F t, ∀ d ∈ contactSites F,
      out.colors d = some (σ d))

theorem measurable_prefix_contact (R : RootPair) (K : Finset (Site 2))
    (b i : ℕ) (t : ℝ) :
    MeasurableSet[fullHistory R (stagePrefix b i)]
      (continuationContactEvent (initialSampler R) (stagePrefix b i) (sourceWindow K b i) t) :=
  measurable_contact_fullHistory R _ _ t

/-- Disjoint finite color patterns identify the full contact event with a covering query. -/
theorem contact_law_eq_sampler (R : RootPair) (L : List (Site 2))
    (F : Finset (Site 2)) (t : ℝ) (hL : ∀ d ∈ contactSites F, d ∈ L) :
    wilsonColorLaw R (contactEvent F t) =
      wilsonRows (continuationContactEvent (initialSampler R) L F t) := by
  let D := contactSites F
  let P := {p : D → Bool // ∃ σ ∈ contactEvent F t, ∀ d : D, σ d.val = p d}
  letI : Fintype P := Fintype.ofFinite P
  let representative (p : P) : ColorField := Classical.choose p.property
  have hrep (p : P) : representative p ∈ contactEvent F t ∧
      ∀ d : D, representative p d.val = p.val d := Classical.choose_spec p.property
  let B (p : P) : Set ColorField := {σ | ∀ d ∈ D, σ d = representative p d}
  let A (p : P) := continuationPattern (initialSampler R) L D (representative p)
  have hBunion : (⋃ p : P, B p) = contactEvent F t := by
    ext σ
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨p, hp⟩
      change t ≤ (contacts F σ : ℝ)
      rw [contacts_of_agree F (fun d hd => hp d hd)]
      exact (hrep p).1
    · intro hσ
      let p : P := ⟨fun d => σ d.val, σ, hσ, fun _ => rfl⟩
      exact ⟨p, fun d hd => ((hrep p).2 ⟨d, hd⟩).symm⟩
  have hAunion : (⋃ p : P, A p) =
      continuationContactEvent (initialSampler R) L F t := by
    ext ξ
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨p, next, hn, hp⟩
      exact ⟨next, hn, representative p, (hrep p).1, hp⟩
    · rintro ⟨next, hn, σ, hσ, hp⟩
      let p : P := ⟨fun d => σ d.val, σ, hσ, fun _ => rfl⟩
      refine ⟨p, next, hn, fun d hd => ?_⟩
      rw [hp d hd]
      exact congrArg some ((hrep p).2 ⟨d, hd⟩).symm
  have hBdisjoint : Pairwise (fun p q => Disjoint (B p) (B q)) := by
    intro p q hpq
    apply Set.disjoint_left.mpr
    intro σ hp hq
    apply hpq
    apply Subtype.ext
    funext d
    calc
      p.val d = representative p d.val := ((hrep p).2 d).symm
      _ = σ d.val := (hp d.val d.property).symm
      _ = representative q d.val := hq d.val d.property
      _ = q.val d := (hrep q).2 d
  have hAdisjoint : Pairwise (fun p q => Disjoint (A p) (A q)) := by
    intro p q hpq
    apply Set.disjoint_left.mpr
    rintro ξ ⟨next, hn, hp⟩ ⟨next', hn', hq⟩
    have he : next = next' := Option.some.inj (hn.symm.trans hn')
    subst next'
    apply hpq
    apply Subtype.ext
    funext d
    calc
      p.val d = representative p d.val := ((hrep p).2 d).symm
      _ = representative q d.val := Option.some.inj
        ((hp d.val d.property).symm.trans (hq d.val d.property))
      _ = q.val d := (hrep q).2 d
  have hBm (p : P) : MeasurableSet (B p) := by
    have he : B p = ⋂ d ∈ D, {σ : ColorField | σ d = representative p d} := by
      ext σ
      simp only [B, Set.mem_setOf_eq, Set.mem_iInter]
    rw [he]
    exact Finset.measurableSet_biInter D (fun d _ =>
      (isClosed_eq (continuous_apply d : Continuous (fun σ : ColorField => σ d))
        continuous_const).measurableSet)
  have hAm (p : P) : MeasurableSet (A p) := measurable_continuationPattern _ _ _ _
  have hmass (p : P) : wilsonColorLaw R (B p) = wilsonRows (A p) :=
    wilsonColorLaw_apply_sampler R L D (representative p) hL
  rw [← hBunion, ← hAunion, measure_iUnion hBdisjoint hBm, measure_iUnion hAdisjoint hAm]
  exact tsum_congr hmass

theorem prefix_contact_law (R : RootPair) (K : Finset (Site 2))
    (b : ℕ) (hb : 6 ≤ b) (i : ℕ) (hi : 1 ≤ i) (t : ℝ) :
    wilsonRows.real
        (continuationContactEvent (initialSampler R) (stagePrefix b i) (sourceWindow K b i) t) =
      (wilsonColorLaw R).real (contactEvent (sourceWindow K b i) t) :=
  congrArg ENNReal.toReal (contact_law_eq_sampler R (stagePrefix b i) (sourceWindow K b i) t
    (fun d hd => source_and_contact_queried K b hb i hi d
      (Finset.mem_union.mpr (Or.inr hd)))).symm

end
end FiniteAvalanches.Wilson.Lattice.CurrentNestedPrefix
