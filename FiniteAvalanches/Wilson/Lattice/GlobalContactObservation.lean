import FiniteAvalanches.Wilson.Lattice.ContactRestriction

/-! Finite-pattern identification of the whole original-incidence contact count. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.GlobalContactObservation
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory
open BatchRestart ConditionalIteration7 ActualContactHistory ActualContactRestriction
open scoped Classical
noncomputable section

/-- A low whole-set count observed only through genuine known endpoint colors. -/
def lowContactObservation (st : SamplerState) (L : List (Site 2))
    (K : Finset (Site 2)) (t : ℝ) : Set Rows :=
  {ξ | ∃ out, samplerRun st L ξ = some out ∧
    ∃ σ : ColorField, (contacts K σ : ℝ) < t ∧
      ∀ d ∈ contactSites K, out.colors d = some (σ d)}

theorem measurable_low_contact_event (K : Finset (Site 2)) (t : ℝ) :
    MeasurableSet {σ : ColorField | (contacts K σ : ℝ) < t} := by
  have he : {σ : ColorField | (contacts K σ : ℝ) < t} = (contactEvent K t)ᶜ := by
    ext σ
    change (contacts K σ : ℝ) < t ↔ ¬ t ≤ (contacts K σ : ℝ)
    exact lt_iff_not_ge
  rw [he]
  exact (measurableSet_contactEvent K t).compl

theorem measurable_lowContactObservation (st : SamplerState) (L : List (Site 2))
    (K : Finset (Site 2)) (t : ℝ) : MeasurableSet (lowContactObservation st L K t) := by
  apply IsOpen.measurableSet
  apply isOpen_iff_mem_nhds.mpr
  rintro ξ ⟨out, hs, σ, hσ, hc⟩
  filter_upwards [samplerRun_eventually_eq_of_some st out L ξ hs] with η hη
  exact ⟨out, hη, σ, hσ, hc⟩

/-- Partitioning by every endpoint color preserves the whole count, including
all original edges absent from the sampled forest and repeated incidences. -/
theorem wilsonColorLaw_low_eq_sampler_low (R : RootPair) (L : List (Site 2))
    (K : Finset (Site 2)) (t : ℝ) (hL : ∀ d ∈ contactSites K, d ∈ L) :
    wilsonColorLaw R {σ : ColorField | (contacts K σ : ℝ) < t} =
      wilsonRows (lowContactObservation (initialSampler R) L K t) := by
  let D := contactSites K
  let P := {p : D → Bool // ∃ σ : ColorField, (contacts K σ : ℝ) < t ∧
    ∀ d : D, σ d.val = p d}
  letI : Fintype P := Fintype.ofFinite P
  let representative (p : P) : ColorField := Classical.choose p.property
  have hrep (p : P) : (contacts K (representative p) : ℝ) < t ∧
      ∀ d : D, representative p d.val = p.val d := Classical.choose_spec p.property
  let B (p : P) : Set ColorField := {σ | ∀ d ∈ D, σ d = representative p d}
  let A (p : P) := continuationPattern (initialSampler R) L D (representative p)
  have hBunion : (⋃ p : P, B p) = {σ : ColorField | (contacts K σ : ℝ) < t} := by
    ext σ
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨p, hp⟩
      rw [contacts_of_agree K (fun d hd => hp d hd)]
      exact (hrep p).1
    · intro hσ
      let p : P := ⟨fun d => σ d.val, σ, hσ, fun _ => rfl⟩
      exact ⟨p, fun d hd => ((hrep p).2 ⟨d, hd⟩).symm⟩
  have hAunion : (⋃ p : P, A p) = lowContactObservation (initialSampler R) L K t := by
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

end
end FiniteAvalanches.Wilson.Lattice.GlobalContactObservation
