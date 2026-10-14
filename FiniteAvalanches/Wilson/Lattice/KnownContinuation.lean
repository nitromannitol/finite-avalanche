import FiniteAvalanches.Wilson.Lattice.ConditionalHistory
import FiniteAvalanches.Wilson.Lattice.NestedPrefixContacts

/-! The source511 remaining-walk law for observations already colored by the
actual earlier prefix or requested by its genuine new continuation. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.CurrentKnownContinuation
open LatticeProb MeasureTheory ProbabilityTheory Filter BatchRestart ConditionalIteration7
open scoped Classical
noncomputable section

/-- Appended known queries consume their actual rows and change no complete output.
Failed original continuations stay failed. No replacement state is assigned. -/
theorem samplerRun_append_known (st : SamplerState) (Q A : List (Site 2))
    (ξ : Rows) (hA : ∀ a ∈ A, a ∈ st.covered ∨ a ∈ Q) :
    samplerRun st (Q ++ A) ξ = samplerRun st Q ξ := by
  rw [samplerRun_append]
  cases hs : samplerRun st Q ξ with
  | none => rfl
  | some next =>
    have hc : ∀ a ∈ A, a ∈ next.covered := by
      intro a ha
      rcases hA a ha with ha | ha
      · change next.colors a ≠ none
        rw [samplerRun_preserves_covered_colors st next Q ξ hs a ha]
        exact ha
      · exact CurrentNestedPrefix.samplerRun_covers_queries st next Q ξ hs a ha
    exact samplerRun_of_covered next A hc _

/-- The literal successful color event is unchanged by appending observed sites
already covered by the initial state or the actual successful new queries. -/
theorem continuationPattern_append_known (st : SamplerState) (Q : List (Site 2))
    (D : Finset (Site 2)) (pc : Site 2 → Bool)
    (hD : ∀ d ∈ D, d ∈ st.covered ∨ d ∈ Q) :
    continuationPattern st (Q ++ D.toList) D pc = continuationPattern st Q D pc := by
  ext ξ
  change (∃ next, samplerRun st (Q ++ D.toList) ξ = some next ∧
    ∀ d ∈ D, next.colors d = some (pc d)) ↔
    (∃ next, samplerRun st Q ξ = some next ∧ ∀ d ∈ D, next.colors d = some (pc d))
  rw [samplerRun_append_known st Q D.toList ξ
    (fun d hd => hD d (Finset.mem_toList.mp hd))]

/-- Padding is invisible on the whole genuine earlier-output atom, including full history. -/
theorem history_inter_continuation_append_known (R : RootPair) (L Q : List (Site 2))
    (out : SamplerState) (D : Finset (Site 2)) (pc : Site 2 → Bool)
    (hD : ∀ d ∈ D, d ∈ out.covered ∨ d ∈ Q) :
    historyAtom R L out ∩ continuationPattern (initialSampler R) (L ++ (Q ++ D.toList)) D pc =
      historyAtom R L out ∩ continuationPattern (initialSampler R) (L ++ Q) D pc := by
  rw [history_inter_continuation_eq R L (Q ++ D.toList) out D pc,
    history_inter_continuation_eq R L Q out D pc,
    continuationPattern_append_known out Q D pc hD]

/-- The actual enlarged-root conditional color law needs only old-known or new-query
coverage. The earlier state and its restarted roots are the same witnesses throughout. -/
theorem conditional_continuation_color_law_known (R : RootPair) (L Q : List (Site 2))
    (ξ₀ : Rows) (out : SamplerState) (hs : samplerRun (initialSampler R) L ξ₀ = some out)
    (D : Finset (Site 2)) (pc : Site 2 → Bool)
    (hD : ∀ d ∈ D, d ∈ out.covered ∨ d ∈ Q) :
    ∀ᵐ ξ ∂wilsonRows, ξ ∈ historyAtom R L out →
      (wilsonRows[(continuationPattern (initialSampler R) (L ++ Q) D pc).indicator
        (fun _ => (1 : ℝ)) | fullHistory R L]) ξ =
      (wilsonColorLaw (restartedRoots R L ξ₀ out hs)).real {σ | ∀ d ∈ D, σ d = pc d} := by
  let H := historyAtom R L out
  let S := continuationPattern (initialSampler R) (L ++ Q) D pc
  let T := continuationPattern (initialSampler R) (L ++ (Q ++ D.toList)) D pc
  have hH : MeasurableSet[fullHistory R L] H := measurable_historyAtom R L out
  have hS : MeasurableSet S := measurable_continuationPattern _ _ _ _
  have hT : MeasurableSet T := measurable_continuationPattern _ _ _ _
  have heq : H.indicator (S.indicator (fun _ => (1 : ℝ))) =
      H.indicator (T.indicator (fun _ => (1 : ℝ))) := by
    rw [Set.indicator_indicator, Set.indicator_indicator]
    exact congrArg (fun A : Set Rows => A.indicator (fun _ => (1 : ℝ)))
      (history_inter_continuation_append_known R L Q out D pc hD).symm
  have hc := condExp_congr_ae (μ := wilsonRows) (m := fullHistory R L)
    (Eventually.of_forall (congrFun heq))
  have hcs := condExp_indicator (μ := wilsonRows) (m := fullHistory R L)
    ((integrable_const (1 : ℝ)).indicator hS) hH
  have hct := condExp_indicator (μ := wilsonRows) (m := fullHistory R L)
    ((integrable_const (1 : ℝ)).indicator hT) hH
  have hlaw := conditional_continuation_color_law R L (Q ++ D.toList) ξ₀ out hs D pc
    (fun d hd => List.mem_append_right Q (Finset.mem_toList.mpr hd))
  filter_upwards [hc, hcs, hct, hlaw] with ξ hc hcs hct hlaw hξ
  have hh : ξ ∈ H := hξ
  simp only [Set.indicator_of_mem hh] at hcs hct
  rw [hcs, hct, hlaw hξ] at hc
  exact hc


/-- On an actual earlier atom even the complete Option-valued later state is unchanged. -/
theorem history_run_append_known (R : RootPair) (L Q A : List (Site 2))
    (out : SamplerState) (hA : ∀ a ∈ A, a ∈ out.covered ∨ a ∈ Q)
    (ξ : Rows) (hh : ξ ∈ historyAtom R L out) :
    samplerRun (initialSampler R) (L ++ (Q ++ A)) ξ =
      samplerRun (initialSampler R) (L ++ Q) ξ := by
  change samplerRun (initialSampler R) L ξ = some out at hh
  rw [samplerRun_append, samplerRun_append, hh, Option.bind_some, Option.bind_some]
  exact samplerRun_append_known out Q A _ hA

/-- Every completed-state observation, including full traces, is unchanged on the same atom. -/
theorem history_inter_completed_append_known (R : RootPair) (L Q A : List (Site 2))
    (out : SamplerState) (hA : ∀ a ∈ A, a ∈ out.covered ∨ a ∈ Q)
    (P : SamplerState → Prop) :
    historyAtom R L out ∩ {ξ : Rows | ∃ next,
      samplerRun (initialSampler R) (L ++ (Q ++ A)) ξ = some next ∧ P next} =
    historyAtom R L out ∩ {ξ : Rows | ∃ next,
      samplerRun (initialSampler R) (L ++ Q) ξ = some next ∧ P next} := by
  ext ξ
  constructor
  · rintro ⟨hh, next, hs, hp⟩
    exact ⟨hh, next, (history_run_append_known R L Q A out hA ξ hh) ▸ hs, hp⟩
  · rintro ⟨hh, next, hs, hp⟩
    exact ⟨hh, next, (history_run_append_known R L Q A out hA ξ hh).symm ▸ hs, hp⟩

/-- Finite contact-event mass transfers when each observed neighbor is old-known
or requested by the new continuation. No contact probability estimate is a premise. -/
theorem history_contact_success_mass_known (R : RootPair) (L Q : List (Site 2))
    (ξ₀ : Rows) (out : SamplerState) (hs : samplerRun (initialSampler R) L ξ₀ = some out)
    (F : Finset (Site 2)) (t : ℝ)
    (hQ : ∀ d ∈ contactSites F, d ∈ out.covered ∨ d ∈ Q) :
    (wilsonColorLaw (restartedRoots R L ξ₀ out hs)).real (contactEvent F t) *
        wilsonRows.real (historyAtom R L out) ≤
      wilsonRows.real (historyAtom R L out ∩
        ActualContactHistory.continuationContactEvent (initialSampler R) (L ++ Q) F t) := by
  have hmass := ActualContactHistory.history_contact_success_mass R L
    (Q ++ (contactSites F).toList) ξ₀ out hs F t
    (fun d hd => List.mem_append_right Q (Finset.mem_toList.mpr hd))
  have he : historyAtom R L out ∩
      ActualContactHistory.continuationContactEvent (initialSampler R)
        (L ++ (Q ++ (contactSites F).toList)) F t =
      historyAtom R L out ∩
        ActualContactHistory.continuationContactEvent (initialSampler R) (L ++ Q) F t :=
    history_inter_completed_append_known R L Q (contactSites F).toList out
      (fun d hd => hQ d (Finset.mem_toList.mp hd))
      (fun next => ∃ σ ∈ contactEvent F t,
        ∀ d ∈ contactSites F, next.colors d = some (σ d))
  rw [he] at hmass
  exact hmass

end
end FiniteAvalanches.Wilson.Lattice.CurrentKnownContinuation
