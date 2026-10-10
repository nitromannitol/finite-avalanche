import FiniteAvalanches.Wilson.CopiedWalk

/-! Measurability of copied first-hit exploration, including unbounded complete
histories and failure. Finite prefixes determine the finite stopped operations. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.CopiedNetwork
open Quiver MeasureTheory ProbabilityTheory FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E I : Type} [Fintype V] [Fintype E] [Countable I] (G : Multigraph V E)

instance stateCountable : Countable (State (V := V) (E := E) (I := I)) :=
  Function.Injective.countable (f := fun s : State (V := V) (E := E) => (s.roots, s.edges, s.history))
    (fun _ _ h => State.ext (congrArg (fun p => p.1) h)
      (congrArg (fun p => p.2.1) h) (congrArg (fun p => p.2.2) h))
instance stateMeasurableSpace : MeasurableSpace (State (V := V) (E := E) (I := I)) := ⊤
instance stateMeasurableSingletonClass : MeasurableSingletonClass (State (V := V) (E := E) (I := I)) :=
  ⟨fun _ => trivial⟩
instance outcomeMeasurableSpace : MeasurableSpace (Option (State (V := V) (E := E) (I := I))) := ⊤
instance outcomeMeasurableSingletonClass : MeasurableSingletonClass (Option (State (V := V) (E := E) (I := I))) :=
  ⟨fun _ => trivial⟩

private def extendPacked {x : V} (p : Σ b : V, Trace G x b) (a : Letter G) : Σ b : V, Trace G x b :=
  letI := pathQuiver G
  ⟨other G p.1 (a p.1), p.2.cons (arrow G p.1 a)⟩

omit [Countable I] in
theorem packedPath_eq_of_prefix (x : V) (ω η : Driver G) (n : ℕ)
    (h : ∀ k < n, ω k = η k) : packedPath G x ω n = packedPath G x η n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change extendPacked G (packedPath G x ω n) (ω n) = extendPacked G (packedPath G x η n) (η n)
    rw [ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h n (Nat.lt_succ_self n)]

variable (ι : E ↪ I)

omit [Countable I] in
theorem attachAt_eq_of_prefix (s : State (V := V) (E := E) (I := I)) (x : V) (ω η : Driver G)
    (n : ℕ) (h : ∀ k < n, ω k = η k) : attachAt G ι s x ω n = attachAt G ι s x η n := by
  apply State.ext
  all_goals dsimp only [attachAt]; rw [packedPath_eq_of_prefix G x ω η n h]

variable [Nonempty (Letter G)]

private def extendPrefix (n : ℕ) (f : Fin n → Letter G) : Driver G :=
  fun k => if h : k < n then f ⟨k, h⟩ else Classical.ofNonempty

omit [Countable I] in
theorem measurable_attachAt (s : State (V := V) (E := E) (I := I)) (x : V) (n : ℕ) :
    Measurable (fun ω : Driver G => attachAt G ι s x ω n) := by
  have hm : Measurable (fun ω : Driver G => attachAt G ι s x (extendPrefix G n (fun i => ω i)) n) :=
    (measurable_of_countable (fun f : Fin n → Letter G => attachAt G ι s x (extendPrefix G n f) n)).comp
      (measurable_pi_lambda _ (fun i => measurable_pi_apply i.val))
  have he : (fun ω : Driver G => attachAt G ι s x ω n) =
      (fun ω => attachAt G ι s x (extendPrefix G n (fun i => ω i)) n) := by
    funext ω
    apply attachAt_eq_of_prefix
    intro k hk
    simp [extendPrefix, hk]
  rw [he]
  exact hm

omit [Nonempty (Letter G)] in
omit [Countable I] in
theorem measurable_position (x : V) (n : ℕ) :
    @Measurable _ _ _ (⊤ : MeasurableSpace V) (fun ω : Driver G => position G x ω n) := by
  letI : MeasurableSpace V := ⊤
  letI : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (measurable_of_countable (fun p : V × Letter G => other G p.1 (p.2 p.1))).comp
      (ih.prodMk (measurable_pi_apply n))

omit [Nonempty (Letter G)] in
omit [Countable I] in
theorem measurableSet_hits (B : Set V) (x : V) : MeasurableSet {ω : Driver G | hits G B x ω} := by
  letI : MeasurableSpace V := ⊤
  have he : {ω : Driver G | hits G B x ω} = ⋃ n : ℕ, {ω | position G x ω n ∈ B} := by
    ext ω; simp [hits]
  rw [he]
  exact MeasurableSet.iUnion (fun n => (measurable_position G x n) (show MeasurableSet B from trivial))

omit [Countable I] in
theorem measurable_attach (s : State (V := V) (E := E) (I := I)) (x : V) :
    Measurable (fun ω : {ω : Driver G // hits G s.roots x ω} => attachAt G ι s x ω.val (Nat.find ω.property)) := by
  letI : MeasurableSpace V := ⊤
  exact Measurable.find (fun n => (measurable_attachAt G ι s x n).comp measurable_subtype_coe)
    (fun n => ((measurable_position G x n) (show MeasurableSet s.roots from trivial)).preimage
      measurable_subtype_coe) (fun ω => ω.property)

theorem measurable_query (s : State (V := V) (E := E) (I := I)) (x : V) : Measurable (query G ι s x) := by
  unfold query
  split
  · exact measurable_const
  · exact ((measurable_of_countable (some : State (V := V) (E := E) → Option (State (V := V) (E := E) (I := I)))).comp
      (measurable_attach G ι s x)).dite measurable_const (measurableSet_hits G s.roots x)

theorem measurable_explore (s : State (V := V) (E := E) (I := I)) (order : List V) :
    Measurable (explore G ι s order) := by
  induction order generalizing s with
  | nil => exact measurable_const
  | cons x xs ih =>
    have hb : Measurable (fun p : Option (State (V := V) (E := E) (I := I)) × (ℕ → Driver G) =>
        p.1.bind (fun t => explore G ι t xs p.2)) := by
      apply measurable_from_prod_countable_right
      intro o
      cases o with
      | none => exact measurable_const
      | some t => exact ih t
    exact hb.comp (((measurable_query G ι s x).comp (measurable_pi_apply 0)).prodMk
      (measurable_pi_lambda _ (fun i => measurable_pi_apply (i + 1))))

/-- This is the actual algorithm's push-forward, with nontermination retained as `none`. -/
def explorationLaw (μ : Measure (Letter G)) (s : State (V := V) (E := E) (I := I)) (order : List V) :
    Measure (Option (State (V := V) (E := E) (I := I))) := (driversLaw G μ).map (explore G ι s order)

instance explorationLaw_probability (μ : Measure (Letter G)) [IsProbabilityMeasure μ]
    (s : State (V := V) (E := E) (I := I)) (order : List V) : IsProbabilityMeasure (explorationLaw G ι μ s order) := by
  letI : IsProbabilityMeasure (driversLaw G μ) := by unfold driversLaw; infer_instance
  exact Measure.isProbabilityMeasure_map (measurable_explore G ι s order).aemeasurable

end
end FiniteAvalanches.Wilson.CopiedNetwork
