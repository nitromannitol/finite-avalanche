import FiniteAvalanches.Wilson.Lattice.ContactHistory

/-! Actual contact success after any observed consumed-row prefix. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.ActualContactRestriction
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory ProbabilityTheory
open BatchRestart ConditionalIteration7 ActualContactHistory
open scoped Classical
noncomputable section

theorem freshRows_indep_consumed (n : ℕ) :
    Indep (freshRows n) (consumedRows n) wilsonRows := by
  have hi : iIndep rowSigma wilsonRows :=
    iIndepFun_infinitePi (P := fun _ : ℕ => walkLaw) (X := fun _ (w : WalkDriver) => w)
      (fun _ => measurable_id)
  exact indep_iSup_of_disjoint rowSigma_le hi
    (Set.disjoint_left.mpr (fun _ hi hj => Nat.not_lt_of_ge hi hj))

theorem measurable_continuationContactEvent (st : SamplerState) (Q : List (Site 2))
    (F : Finset (Site 2)) (t : ℝ) :
    MeasurableSet (continuationContactEvent st Q F t) := by
  apply IsOpen.measurableSet
  apply isOpen_iff_mem_nhds.mpr
  rintro ξ ⟨out, hs, σ, hσ, hc⟩
  filter_upwards [samplerRun_eventually_eq_of_some st out Q ξ hs] with η hη
  exact ⟨out, hη, σ, hσ, hc⟩

theorem measurable_contact_success_consumed (R : RootPair) (L : List (Site 2))
    (F : Finset (Site 2)) (t : ℝ) :
    MeasurableSet[consumedRows L.length]
      (continuationContactEvent (initialSampler R) L F t) :=
  fullHistory_le_consumed R L _ (measurable_completed_observation R L
    (fun out => ∃ σ ∈ contactEvent F t, ∀ d ∈ contactSites F,
      out.colors d = some (σ d)))

theorem history_contact_success_mass_restricted (R : RootPair) (L Q : List (Site 2))
    (ξ₀ : Rows) (out : SamplerState) (hs : samplerRun (initialSampler R) L ξ₀ = some out)
    (E : Set Rows) (hE : MeasurableSet[consumedRows L.length] E)
    (F : Finset (Site 2)) (t : ℝ) (hQ : ∀ d ∈ contactSites F, d ∈ Q) :
    (wilsonColorLaw (restartedRoots R L ξ₀ out hs)).real (contactEvent F t) *
        wilsonRows.real (E ∩ historyAtom R L out) ≤
      wilsonRows.real ((E ∩ historyAtom R L out) ∩
        continuationContactEvent (initialSampler R) (L ++ Q) F t) := by
  let D := contactSites F
  let P := {p : D → Bool // ∃ σ ∈ contactEvent F t, ∀ d : D, σ d.val = p d}
  letI : Fintype P := Fintype.ofFinite P
  let representative (p : P) : ColorField := Classical.choose p.property
  have hrep (p : P) : representative p ∈ contactEvent F t ∧
      ∀ d : D, representative p d.val = p.val d := Classical.choose_spec p.property
  let B (p : P) : Set ColorField := {σ | ∀ d ∈ D, σ d = representative p d}
  let A (p : P) := continuationPattern (initialSampler R) (L ++ Q) D (representative p)
  let H := E ∩ historyAtom R L out
  have hBunion : (⋃ p : P, B p) = contactEvent F t := by
    ext σ
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨p, hp⟩
      have he := contacts_of_agree F (fun d hd => hp d hd)
      change t ≤ (contacts F σ : ℝ)
      rw [he]
      exact (hrep p).1
    · intro hσ
      let p : P := ⟨fun d => σ d.val, σ, hσ, fun _ => rfl⟩
      refine ⟨p, fun d hd => ?_⟩
      exact ((hrep p).2 ⟨d, hd⟩).symm
  have hAunion : (⋃ p : P, A p) =
      continuationContactEvent (initialSampler R) (L ++ Q) F t := by
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
  have hHc : MeasurableSet[consumedRows L.length] H :=
    hE.inter (measurable_historyAtom_consumed R L out)
  have hH : MeasurableSet H := consumedRows_le L.length H hHc
  have hmass (p : P) :
      (wilsonColorLaw (restartedRoots R L ξ₀ out hs)).real (B p) * wilsonRows.real H ≤
        wilsonRows.real (H ∩ A p) := by
    let T := (fun ξ : Rows => fun i => ξ (i + L.length)) ⁻¹'
      continuationPattern out Q D (representative p)
    have hTf : MeasurableSet[freshRows L.length] T :=
      (measurable_continuationPattern out Q D (representative p)).preimage
        (measurable_tail_fresh L.length)
    have ht : wilsonRows.real T =
        (wilsonColorLaw (restartedRoots R L ξ₀ out hs)).real (B p) := by
      change (wilsonRows T).toReal = _
      rw [← Measure.map_apply (by fun_prop : Measurable
        (fun ξ : Rows => fun i => ξ (i + L.length)))
        (measurable_continuationPattern out Q D (representative p)), tail_map_wilsonRows]
      exact congrArg ENNReal.toReal
        (fresh_continuation_color_pattern_law R L Q ξ₀ out hs D (representative p) hQ).symm
    have he : H ∩ A p = H ∩ T := by
      change (E ∩ historyAtom R L out) ∩
        continuationPattern (initialSampler R) (L ++ Q) D (representative p) = _
      rw [Set.inter_assoc, history_inter_continuation_eq, ← Set.inter_assoc]
    have hi := (freshRows_indep_consumed L.length).symm.indepSet_of_measurableSet hHc hTf
    rw [he]
    change _ ≤ (wilsonRows (H ∩ T)).toReal
    rw [hi.measure_inter_eq_mul, ENNReal.toReal_mul]
    change _ ≤ wilsonRows.real H * wilsonRows.real T
    rw [ht, mul_comm]
  have hIdisjoint : Pairwise (fun p q => Disjoint (H ∩ A p) (H ∩ A q)) := by
    intro p q hpq
    exact (hAdisjoint hpq).mono Set.inter_subset_right Set.inter_subset_right
  calc
    _ = (∑ p : P, (wilsonColorLaw (restartedRoots R L ξ₀ out hs)).real (B p)) *
        wilsonRows.real H := by
      rw [← hBunion, measureReal_iUnion_fintype hBdisjoint hBm]
    _ = ∑ p : P, (wilsonColorLaw (restartedRoots R L ξ₀ out hs)).real (B p) *
        wilsonRows.real H := Finset.sum_mul _ _ _
    _ ≤ ∑ p : P, wilsonRows.real (H ∩ A p) := Finset.sum_le_sum (fun p _ => hmass p)
    _ = wilsonRows.real (H ∩ continuationContactEvent (initialSampler R) (L ++ Q) F t) := by
      rw [← measureReal_iUnion_fintype hIdisjoint (fun p => hH.inter (hAm p)),
        ← Set.inter_iUnion, hAunion]


end
end FiniteAvalanches.Wilson.Lattice.ActualContactRestriction
