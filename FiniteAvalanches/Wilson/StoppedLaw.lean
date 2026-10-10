import FiniteAvalanches.Wilson.PrefixTransport

/-! First-hit observables have a realization-independent law, with genuine
nontermination retained. Complete prefixes determine the actual stopped path;
chronological erasure is applied only afterwards. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.CopiedNetwork
open MeasureTheory ProbabilityTheory FiniteAvalanches.Trees
open scoped Classical ENNReal
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)

private theorem prefix_event (x : V) (n : ℕ) (P : Driver G → Prop)
    (hP : ∀ ω η, walkPrefix G x ω n = walkPrefix G x η n → (P ω ↔ P η)) :
    ∃ U : Set (PrefixRecord (V := V) (E := E)), MeasurableSet U ∧
      {ω | P ω} = (fun ω => walkPrefix G x ω n) ⁻¹' U := by
  let U : Set (PrefixRecord (V := V) (E := E)) := {p | ∀ ω, walkPrefix G x ω n = p → P ω}
  refine ⟨U, trivial, ?_⟩
  ext ω
  constructor
  · intro hp η he
    exact (hP ω η he.symm).mp hp
  · intro hu
    exact hu ω rfl

variable [∀ v : V, MeasurableSpace (Incident G v)] [∀ v : V, MeasurableSingletonClass (Incident G v)]
variable (μ ν : Measure (Letter G)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

private theorem prefix_event_measure_eq
    (h : ∀ v : V, μ.map (fun a => a v) = ν.map (fun a => a v))
    (x : V) (n : ℕ) (P : Driver G → Prop)
    (hP : ∀ ω η, walkPrefix G x ω n = walkPrefix G x η n → (P ω ↔ P η)) :
    driverLaw G μ {ω | P ω} = driverLaw G ν {ω | P ω} := by
  obtain ⟨U, hU, he⟩ := prefix_event G x n P hP
  rw [he, ← Measure.map_apply (measurable_walkPrefix G x n) hU,
    ← Measure.map_apply (measurable_walkPrefix G x n) hU, walkPrefix_law_eq G μ ν h]

private theorem first_hit_event_measure_eq
    (h : ∀ v : V, μ.map (fun a => a v) = ν.map (fun a => a v))
    (B : Set V) (x : V) (P : Driver G → ℕ → Prop)
    (hP : ∀ n ω η, walkPrefix G x ω n = walkPrefix G x η n → (P ω n ↔ P η n)) :
    driverLaw G μ {ω | ∃ n, firstHitAt G B x ω n ∧ P ω n} =
      driverLaw G ν {ω | ∃ n, firstHitAt G B x ω n ∧ P ω n} := by
  let A : ℕ → Set (Driver G) := fun n => {ω | firstHitAt G B x ω n ∧ P ω n}
  have hm (n : ℕ) : MeasurableSet (A n) := by
    obtain ⟨U, hU, he⟩ := prefix_event G x n (fun ω => firstHitAt G B x ω n ∧ P ω n)
      (fun ω η hh => and_congr (firstHitAt_eq_of_walkPrefix_eq G B x ω η n hh) (hP n ω η hh))
    change MeasurableSet {ω | firstHitAt G B x ω n ∧ P ω n}
    rw [he]
    exact (measurable_walkPrefix G x n) hU
  have hd : Pairwise (fun n m => Disjoint (A n) (A m)) := by
    intro n m hnm
    exact Set.disjoint_left.mpr (fun ω hn hm => hnm (firstHitAt_unique G B x ω hn.1 hm.1))
  have he : {ω : Driver G | ∃ n, firstHitAt G B x ω n ∧ P ω n} = ⋃ n, A n := by ext ω; simp [A]
  rw [he, measure_iUnion hd hm, measure_iUnion hd hm]
  apply tsum_congr
  intro n
  exact prefix_event_measure_eq G μ ν h x n _
    (fun ω η hh => and_congr (firstHitAt_eq_of_walkPrefix_eq G B x ω η n hh) (hP n ω η hh))

theorem hits_measure_eq
    (h : ∀ v : V, μ.map (fun a => a v) = ν.map (fun a => a v)) (B : Set V) (x : V) :
    driverLaw G μ {ω | hits G B x ω} = driverLaw G ν {ω | hits G B x ω} := by
  have he : {ω : Driver G | hits G B x ω} = {ω | ∃ n, firstHitAt G B x ω n ∧ True} := by
    ext ω
    constructor
    · intro hh
      exact ⟨Nat.find hh, (firstHitAt_iff_find G B x ω _).mpr ⟨hh, rfl⟩, trivial⟩
    · rintro ⟨n, hn, _⟩
      exact ⟨n, hn.1⟩
  rw [he]
  exact first_hit_event_measure_eq G μ ν h B x (fun _ _ => True) (fun _ _ _ _ => Iff.rfl)

variable {O : Type} [Countable O] [MeasurableSpace O] [MeasurableSingletonClass O]
variable [MeasurableSpace (Option O)] [MeasurableSingletonClass (Option O)]

/-- An observable of the actual least hit; none records the absence of a finite hit. -/
def firstHitOutput (B : Set V) (x : V) (f : Driver G → ℕ → O) (ω : Driver G) : Option O :=
  if h : hits G B x ω then some (f ω (Nat.find h)) else none

omit [∀ v : V, MeasurableSpace (Incident G v)] [∀ v : V, MeasurableSingletonClass (Incident G v)] [MeasurableSingletonClass (Option O)] in
theorem measurable_firstHitOutput (B : Set V) (x : V) (f : Driver G → ℕ → O)
    (hf : ∀ n, Measurable (fun ω => f ω n)) : Measurable (firstHitOutput G B x f) := by
  letI : MeasurableSpace V := ⊤
  have hs : Measurable (fun ω : {ω : Driver G // hits G B x ω} => f ω.val (Nat.find ω.property)) :=
    Measurable.find (fun n => (hf n).comp measurable_subtype_coe)
      (fun n => ((measurable_position G x n) (show MeasurableSet B from trivial)).preimage measurable_subtype_coe)
      (fun ω => ω.property)
  exact ((measurable_of_countable (some : O → Option O)).comp hs).dite measurable_const (measurableSet_hits G B x)

omit [∀ v : V, MeasurableSpace (Incident G v)] [∀ v : V, MeasurableSingletonClass (Incident G v)] [Countable O] [MeasurableSpace O]
  [MeasurableSingletonClass O] [MeasurableSpace (Option O)] [MeasurableSingletonClass (Option O)] in
theorem firstHitOutput_eq_some_iff (B : Set V) (x : V) (f : Driver G → ℕ → O)
    (ω : Driver G) (o : O) :
    firstHitOutput G B x f ω = some o ↔ ∃ n, firstHitAt G B x ω n ∧ f ω n = o := by
  unfold firstHitOutput
  split
  · rename_i hh
    constructor
    · intro he
      exact ⟨Nat.find hh, (firstHitAt_iff_find G B x ω _).mpr ⟨hh, rfl⟩, Option.some.inj he⟩
    · rintro ⟨n, hn, he⟩
      obtain ⟨h', hn'⟩ := (firstHitAt_iff_find G B x ω n).mp hn
      simpa only [hn'] using congrArg some he
  · rename_i hh
    constructor
    · intro he; cases he
    · rintro ⟨n, hn, _⟩; exact False.elim (hh ⟨n, hn.1⟩)

theorem firstHitOutput_law_eq
    (h : ∀ v : V, μ.map (fun a => a v) = ν.map (fun a => a v))
    (B : Set V) (x : V) (f : Driver G → ℕ → O) (hf : ∀ n, Measurable (fun ω => f ω n))
    (hfp : ∀ n ω η, walkPrefix G x ω n = walkPrefix G x η n → f ω n = f η n) :
    (driverLaw G μ).map (firstHitOutput G B x f) =
      (driverLaw G ν).map (firstHitOutput G B x f) := by
  apply Measure.ext_of_singleton
  intro o
  rw [Measure.map_apply (measurable_firstHitOutput G B x f hf) (measurableSet_singleton o),
    Measure.map_apply (measurable_firstHitOutput G B x f hf) (measurableSet_singleton o)]
  cases o with
  | some o =>
    have he : firstHitOutput G B x f ⁻¹' {some o} =
        {ω | ∃ n, firstHitAt G B x ω n ∧ f ω n = o} := by
      ext ω; exact firstHitOutput_eq_some_iff G B x f ω o
    rw [he]
    exact first_hit_event_measure_eq G μ ν h B x (fun ω n => f ω n = o)
      (fun n ω η hh => by rw [hfp n ω η hh])
  | none =>
    have he : firstHitOutput G B x f ⁻¹' {none} = {ω | hits G B x ω}ᶜ := by
      ext ω; simp [firstHitOutput]
    rw [he, measure_compl (measurableSet_hits G B x) (measure_ne_top _ _),
      measure_compl (measurableSet_hits G B x) (measure_ne_top _ _), measure_univ, measure_univ,
      hits_measure_eq G μ ν h]

variable {I : Type} [Countable I] (ι : E ↪ I) [Nonempty (Letter G)]

theorem query_law_eq
    (h : ∀ v : V, μ.map (fun a => a v) = ν.map (fun a => a v))
    (s : State (V := V) (E := E) (I := I)) (x : V) :
    (driverLaw G μ).map (query G ι s x) = (driverLaw G ν).map (query G ι s x) := by
  by_cases hx : x ∈ s.roots
  · have he : query G ι s x = fun _ => some s := by funext ω; simp only [query, if_pos hx]
    rw [he]
    simp
  · have he : query G ι s x = firstHitOutput G s.roots x (fun ω n => attachAt G ι s x ω n) := by
      funext ω; simp only [query, if_neg hx, firstHitOutput]
    rw [he]
    exact firstHitOutput_law_eq G μ ν h s.roots x _ (measurable_attachAt G ι s x)
      (fun n ω η hh => attachAt_eq_of_walkPrefix_eq G ι s x ω η n hh)

end
end FiniteAvalanches.Wilson.CopiedNetwork
