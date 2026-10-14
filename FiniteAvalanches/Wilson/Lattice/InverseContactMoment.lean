import FiniteAvalanches.Wilson.Lattice.KnownContinuation
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Current main.tex511 and519–523: the finite observed-neighbor conditional
inverse moment. No color field is assigned to an unknown site or a failed run. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.CurrentInverseContact
open LatticeProb Sandpile MeasureTheory ProbabilityTheory Filter
open ConditionalIteration7 BatchRestart CurrentKnownContinuation CurrentNestedPrefix
open scoped Classical
noncomputable section

/-- Each original origin/neighbor occurrence is counted, even when two origins
share a neighbor. The pattern is defined only on the actual finite neighbor set. -/
def patternContacts (F : Finset (Site 2)) (p : contactSites F → Bool) : ℕ :=
  ∑ x : F, ∑ y : nbrFinset x.val,
    if p ⟨y.val, Finset.mem_biUnion.mpr ⟨x.val, x.property, y.property⟩⟩ then 1 else 0

/-- Literal complete finite color pattern, with arbitrary colors outside it. -/
def fieldPatternEvent (F : Finset (Site 2)) (p : contactSites F → Bool) : Set ColorField :=
  {σ | ∀ d : contactSites F, σ d.val = p d}

/-- A pattern is observed only in the genuine Some output, at every neighbor. -/
def observedPattern (st : SamplerState) (L : List (Site 2)) (F : Finset (Site 2))
    (p : contactSites F → Bool) : Set Rows :=
  {ξ | ∃ next, samplerRun st L ξ = some next ∧
    ∀ d : contactSites F, next.colors d.val = some (p d)}

/-- Outside extensions have no effect on the literal finite contact count. -/
theorem patternContacts_eq_contacts (F : Finset (Site 2)) (p : contactSites F → Bool)
    (σ : ColorField) (hp : ∀ d : contactSites F, σ d.val = p d) :
    patternContacts F p = contacts F σ := by
  unfold patternContacts
  calc
    _ = ∑ x : F, ∑ y : nbrFinset x.val, if σ y.val then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro y _hy
      rw [hp ⟨y.val, Finset.mem_biUnion.mpr ⟨x.val, x.property, y.property⟩⟩]
    _ = ∑ x : F, ∑ y ∈ nbrFinset x.val, if σ y then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact Finset.sum_coe_sort (nbrFinset x.val) (fun y => if σ y then (1 : ℕ) else 0)
    _ = contacts F σ :=
      Finset.sum_coe_sort F (fun x => ∑ y ∈ nbrFinset x, if σ y then (1 : ℕ) else 0)

theorem outside_extensions_agree (F : Finset (Site 2)) (p : contactSites F → Bool)
    (σ τ : ColorField) (hσ : ∀ d : contactSites F, σ d.val = p d)
    (hτ : ∀ d : contactSites F, τ d.val = p d) : contacts F σ = contacts F τ :=
  (patternContacts_eq_contacts F p σ hσ).symm.trans (patternContacts_eq_contacts F p τ hτ)

theorem fieldPatternEvent_eq (F : Finset (Site 2)) (p : contactSites F → Bool)
    (pc : Site 2 → Bool) (hpc : ∀ d : contactSites F, pc d.val = p d) :
    fieldPatternEvent F p = {σ | ∀ d ∈ contactSites F, σ d = pc d} := by
  ext σ
  constructor
  · intro h d hd
    exact (h ⟨d, hd⟩).trans (hpc ⟨d, hd⟩).symm
  · intro h d
    exact (h d.val d.property).trans (hpc d)

theorem observedPattern_eq (st : SamplerState) (L : List (Site 2))
    (F : Finset (Site 2)) (p : contactSites F → Bool) (pc : Site 2 → Bool)
    (hpc : ∀ d : contactSites F, pc d.val = p d) :
    observedPattern st L F p = continuationPattern st L (contactSites F) pc := by
  ext ξ
  constructor
  · rintro ⟨next, hs, hp⟩
    refine ⟨next, hs, ?_⟩
    intro d hd
    rw [hpc ⟨d, hd⟩]
    exact hp ⟨d, hd⟩
  · rintro ⟨next, hs, hp⟩
    refine ⟨next, hs, ?_⟩
    intro d
    rw [← hpc d]
    exact hp d.val d.property

theorem measurable_fieldPatternEvent (F : Finset (Site 2))
    (p : contactSites F → Bool) : MeasurableSet (fieldPatternEvent F p) := by
  have he : fieldPatternEvent F p = ⋂ d : contactSites F, {σ | σ d.val = p d} := by
    ext σ; simp only [fieldPatternEvent, Set.mem_setOf_eq, Set.mem_iInter]
  rw [he]
  exact MeasurableSet.iInter (fun d =>
    (isClosed_eq (continuous_apply d.val : Continuous (fun σ : ColorField => σ d.val))
      continuous_const).measurableSet)

theorem measurable_observedPattern (st : SamplerState) (L : List (Site 2))
    (F : Finset (Site 2)) (p : contactSites F → Bool) :
    MeasurableSet (observedPattern st L F p) := by
  let pc : Site 2 → Bool := fun d => if hd : d ∈ contactSites F then p ⟨d, hd⟩ else false
  have hpc : ∀ d : contactSites F, pc d.val = p d := by
    intro d; exact dif_pos d.property
  rw [observedPattern_eq st L F p pc hpc]
  exact measurable_continuationPattern st L (contactSites F) pc

theorem field_pattern_partition (F : Finset (Site 2)) (σ : ColorField) :
    ∃! p : contactSites F → Bool, σ ∈ fieldPatternEvent F p := by
  refine ⟨fun d => σ d.val, (fun _ => rfl), ?_⟩
  intro p hp
  funext d
  exact (hp d).symm

theorem field_patterns_disjoint (F : Finset (Site 2))
    (p q : contactSites F → Bool) (hne : p ≠ q) :
    Disjoint (fieldPatternEvent F p) (fieldPatternEvent F q) := by
  apply Set.disjoint_left.mpr
  intro σ hp hq
  apply hne
  funext d
  exact (hp d).symm.trans (hq d)

theorem observed_patterns_disjoint (st : SamplerState) (L : List (Site 2))
    (F : Finset (Site 2)) (p q : contactSites F → Bool) (hne : p ≠ q) :
    Disjoint (observedPattern st L F p) (observedPattern st L F q) := by
  apply Set.disjoint_left.mpr
  rintro ξ ⟨next, hs, hp⟩ ⟨next', hs', hq⟩
  have he : next' = next := Option.some.inj (hs'.symm.trans hs)
  subst next'
  apply hne
  funext d
  exact Option.some.inj ((hp d).symm.trans (hq d))

theorem observed_pattern_partition (st : SamplerState) (L : List (Site 2))
    (F : Finset (Site 2)) (ξ : Rows) (next : SamplerState)
    (hs : samplerRun st L ξ = some next)
    (hknown : ∀ d : contactSites F, d.val ∈ next.covered) :
    ∃! p : contactSites F → Bool, ξ ∈ observedPattern st L F p := by
  have hsome : ∀ d : contactSites F, ∃ b : Bool, next.colors d.val = some b := by
    intro d
    cases hc : next.colors d.val with
    | none => exact (hknown d hc).elim
    | some b => exact ⟨b, rfl⟩
  choose p hp using hsome
  refine ⟨p, ⟨next, hs, hp⟩, ?_⟩
  rintro q ⟨next', hs', hq⟩
  have he : next' = next := Option.some.inj (hs'.symm.trans hs)
  subst next'
  funext d
  exact Option.some.inj ((hq d).symm.trans (hp d))

/-- On the same genuine earlier atom, successful continuation has exactly one
complete neighbor pattern. None remains absent from every pattern event. -/
theorem history_pattern_union_eq_success (R : RootPair) (L Q : List (Site 2))
    (out : SamplerState) (F : Finset (Site 2))
    (hD : ∀ d ∈ contactSites F, d ∈ out.covered ∨ d ∈ Q) :
    historyAtom R L out ∩ (⋃ p : contactSites F → Bool,
      observedPattern (initialSampler R) (L ++ Q) F p) =
    historyAtom R L out ∩ {ξ : Rows | ∃ next,
      samplerRun (initialSampler R) (L ++ Q) ξ = some next} := by
  ext ξ
  constructor
  · rintro ⟨hh, hp⟩
    obtain ⟨p, next, hs, _hc⟩ := Set.mem_iUnion.mp hp
    exact ⟨hh, next, hs⟩
  · rintro ⟨hh, next, hs⟩
    have htail : samplerRun out Q (fun k => ξ (k + L.length)) = some next := by
      have hh' : samplerRun (initialSampler R) L ξ = some out := hh
      simpa only [samplerRun_append, hh', Option.bind_some] using hs
    have hk : ∀ d : contactSites F, d.val ∈ next.covered := by
      intro d
      rcases hD d.val d.property with hd | hd
      · change next.colors d.val ≠ none
        rw [samplerRun_preserves_covered_colors out next Q _ htail d.val hd]
        exact hd
      · exact samplerRun_covers_queries out next Q _ htail d.val hd
    obtain ⟨p, hp, _hu⟩ := observed_pattern_partition (initialSampler R) (L ++ Q) F ξ next hs hk
    exact ⟨hh, Set.mem_iUnion.mpr ⟨p, hp⟩⟩

theorem failed_run_no_pattern (st : SamplerState) (L : List (Site 2))
    (F : Finset (Site 2)) (ξ : Rows) (hn : samplerRun st L ξ = none) :
    ∀ p : contactSites F → Bool, ξ ∉ observedPattern st L F p := by
  rintro p ⟨next, hs, _hp⟩
  rw [hn] at hs
  cases hs

/-- Exact finite partition of the actual field inverse, including algebraic inverse0.
No max1 count or invented global completion is used. -/
theorem inverse_contacts_partition (F : Finset (Site 2)) (σ : ColorField) :
    (contacts F σ : ℝ)⁻¹ = ∑ p : contactSites F → Bool,
      (fieldPatternEvent F p).indicator (fun _ => (patternContacts F p : ℝ)⁻¹) σ := by
  let pσ : contactSites F → Bool := fun d => σ d.val
  have hm : σ ∈ fieldPatternEvent F pσ := fun _ => rfl
  rw [Finset.sum_eq_single pσ]
  · rw [Set.indicator_of_mem hm, patternContacts_eq_contacts F pσ σ (fun _ => rfl)]
  · intro q _hq hne
    apply Set.indicator_of_notMem
    intro hq
    exact hne ((field_pattern_partition F σ).unique hq hm)
  · intro hnot
    exact (hnot (Finset.mem_univ pσ)).elim

/-- Finite observed values prove actual integrability of the original inverse,
so its integral is not an unproved nonintegrable default branch. -/
theorem integrable_inverse_contacts (F : Finset (Site 2)) (S : RootPair) :
    Integrable (fun σ => (contacts F σ : ℝ)⁻¹) (wilsonColorLaw S) := by
  have hi : Integrable (fun σ => ∑ p : contactSites F → Bool,
      (fieldPatternEvent F p).indicator (fun _ => (patternContacts F p : ℝ)⁻¹) σ)
      (wilsonColorLaw S) :=
    integrable_finsetSum Finset.univ (fun p _ =>
      (integrable_const _).indicator (measurable_fieldPatternEvent F p))
  exact hi.congr (Eventually.of_forall (fun σ => (inverse_contacts_partition F σ).symm))

theorem inverse_contacts_integral_partition (F : Finset (Site 2)) (S : RootPair) :
    (∫ σ, (contacts F σ : ℝ)⁻¹ ∂wilsonColorLaw S) =
      ∑ p : contactSites F → Bool, (patternContacts F p : ℝ)⁻¹ *
        (wilsonColorLaw S).real (fieldPatternEvent F p) := by
  let f := fun p : contactSites F → Bool =>
    (fieldPatternEvent F p).indicator (fun _ => (patternContacts F p : ℝ)⁻¹)
  have hi (p : contactSites F → Bool) : Integrable (f p) (wilsonColorLaw S) :=
    (integrable_const _).indicator (measurable_fieldPatternEvent F p)
  calc
    _ = ∫ σ, ∑ p : contactSites F → Bool, f p σ ∂wilsonColorLaw S :=
      integral_congr_ae (Eventually.of_forall (inverse_contacts_partition F))
    _ = ∑ p : contactSites F → Bool, ∫ σ, f p σ ∂wilsonColorLaw S :=
      integral_finsetSum Finset.univ (fun p _ => hi p)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [integral_indicator_const _ (measurable_fieldPatternEvent F p), smul_eq_mul, mul_comm]

/-- The known/new-query finite pattern law at the literal subtype pattern. The
temporary extension exists only in this proof, and both events use only its restriction. -/
theorem conditional_observed_pattern_known (R : RootPair) (L Q : List (Site 2))
    (ξ₀ : Rows) (out : SamplerState) (hs : samplerRun (initialSampler R) L ξ₀ = some out)
    (F : Finset (Site 2)) (p : contactSites F → Bool)
    (hD : ∀ d ∈ contactSites F, d ∈ out.covered ∨ d ∈ Q) :
    ∀ᵐ ξ ∂wilsonRows, ξ ∈ historyAtom R L out →
      (wilsonRows[(observedPattern (initialSampler R) (L ++ Q) F p).indicator
        (fun _ => (1 : ℝ)) | fullHistory R L]) ξ =
      (wilsonColorLaw (restartedRoots R L ξ₀ out hs)).real (fieldPatternEvent F p) := by
  let pc : Site 2 → Bool := fun d => if hd : d ∈ contactSites F then p ⟨d, hd⟩ else false
  have hpc : ∀ d : contactSites F, pc d.val = p d := by
    intro d; exact dif_pos d.property
  rw [observedPattern_eq _ _ F p pc hpc, fieldPatternEvent_eq F p pc hpc]
  exact conditional_continuation_color_law_known R L Q ξ₀ out hs (contactSites F) pc hD

/-- The genuine finite conditional inverse-contact moment on the same earlier
complete-output atom and the same restarted roots. No conditional-law or estimate premise. -/
theorem conditional_inverse_contacts_known (R : RootPair) (L Q : List (Site 2))
    (ξ₀ : Rows) (out : SamplerState) (hs : samplerRun (initialSampler R) L ξ₀ = some out)
    (F : Finset (Site 2))
    (hD : ∀ d ∈ contactSites F, d ∈ out.covered ∨ d ∈ Q) :
    ∀ᵐ ξ ∂wilsonRows, ξ ∈ historyAtom R L out →
      (∑ p : contactSites F → Bool, (patternContacts F p : ℝ)⁻¹ *
        (wilsonRows[(observedPattern (initialSampler R) (L ++ Q) F p).indicator
          (fun _ => (1 : ℝ)) | fullHistory R L]) ξ) =
      ∫ σ, (contacts F σ : ℝ)⁻¹ ∂wilsonColorLaw (restartedRoots R L ξ₀ out hs) := by
  have hall : ∀ᵐ ξ ∂wilsonRows, ∀ p : contactSites F → Bool,
      ξ ∈ historyAtom R L out →
        (wilsonRows[(observedPattern (initialSampler R) (L ++ Q) F p).indicator
          (fun _ => (1 : ℝ)) | fullHistory R L]) ξ =
        (wilsonColorLaw (restartedRoots R L ξ₀ out hs)).real (fieldPatternEvent F p) :=
    ae_all_iff.mpr (fun p => conditional_observed_pattern_known R L Q ξ₀ out hs F p hD)
  filter_upwards [hall] with ξ hξ hh
  calc
    _ = ∑ p : contactSites F → Bool, (patternContacts F p : ℝ)⁻¹ *
        (wilsonColorLaw (restartedRoots R L ξ₀ out hs)).real (fieldPatternEvent F p) := by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [hξ p hh]
    _ = _ := (inverse_contacts_integral_partition F (restartedRoots R L ξ₀ out hs)).symm

end
end FiniteAvalanches.Wilson.Lattice.CurrentInverseContact

set_option pp.fullNames true
#print FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.patternContacts
#print axioms FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.patternContacts
#print FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.fieldPatternEvent
#print axioms FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.fieldPatternEvent
#print FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.observedPattern
#print axioms FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.observedPattern
#print FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.patternContacts_eq_contacts
#print axioms FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.patternContacts_eq_contacts
#print FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.outside_extensions_agree
#print axioms FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.outside_extensions_agree
#print FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.fieldPatternEvent_eq
#print axioms FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.fieldPatternEvent_eq
#print FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.observedPattern_eq
#print axioms FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.observedPattern_eq
#print FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.measurable_fieldPatternEvent
#print axioms FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.measurable_fieldPatternEvent
#print FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.measurable_observedPattern
#print axioms FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.measurable_observedPattern
#print FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.field_pattern_partition
#print axioms FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.field_pattern_partition
#print FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.field_patterns_disjoint
#print axioms FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.field_patterns_disjoint
#print FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.observed_patterns_disjoint
#print axioms FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.observed_patterns_disjoint
#print FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.observed_pattern_partition
#print axioms FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.observed_pattern_partition
#print FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.history_pattern_union_eq_success
#print axioms FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.history_pattern_union_eq_success
#print FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.failed_run_no_pattern
#print axioms FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.failed_run_no_pattern
#print FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.inverse_contacts_partition
#print axioms FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.inverse_contacts_partition
#print FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.integrable_inverse_contacts
#print axioms FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.integrable_inverse_contacts
#print FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.inverse_contacts_integral_partition
#print axioms FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.inverse_contacts_integral_partition
#print FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.conditional_observed_pattern_known
#print axioms FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.conditional_observed_pattern_known
#print FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.conditional_inverse_contacts_known
#print axioms FiniteAvalanches.Wilson.Lattice.CurrentInverseContact.conditional_inverse_contacts_known
