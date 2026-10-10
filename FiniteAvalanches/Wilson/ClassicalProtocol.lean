import FiniteAvalanches.Wilson.StoppedLaw
import FiniteAvalanches.Wilson.FreshRows

/-! The classical first-unretained list protocol uses a row only for an actual
walk. The slot protocol discards a fresh row at a skip. Their complete output
laws agree, including histories and nontermination. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.CopiedNetwork
open MeasureTheory ProbabilityTheory FiniteAvalanches.Trees
open scoped Classical ENNReal
noncomputable section
variable {V E I : Type} [Fintype V] [Fintype E]
variable (G : Multigraph V E) (ι : E ↪ I)

def classicalExplore (s : State (V := V) (E := E) (I := I)) :
    List V → (ℕ → Driver G) → Option (State (V := V) (E := E) (I := I))
  | [], _ => some s
  | x :: xs, ω => if x ∈ s.roots then classicalExplore s xs ω
      else (query G ι s x (ω 0)).bind (fun t => classicalExplore t xs (fun i => ω (i + 1)))

theorem classicalExplore_skip_prefix (s : State (V := V) (E := E) (I := I))
    (skips order : List V) (hs : ∀ x ∈ skips, x ∈ s.roots) (ω : ℕ → Driver G) :
    classicalExplore G ι s (skips ++ order) ω = classicalExplore G ι s order ω := by
  induction skips with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, classicalExplore, if_pos (hs x (by simp))]
    exact ih (fun v hv => hs v (by simp [hv]))

theorem classicalExplore_all_roots (s : State (V := V) (E := E) (I := I))
    (hs : s.roots = Set.univ) (order : List V) (ω : ℕ → Driver G) :
    classicalExplore G ι s order ω = some s := by
  induction order with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ∈ s.roots := hs ▸ Set.mem_univ x
    simp only [classicalExplore, if_pos hx]
    exact ih

variable [Countable I] [Nonempty (Letter G)]

theorem measurable_classicalExplore (s : State (V := V) (E := E) (I := I)) (order : List V) :
    Measurable (classicalExplore G ι s order) := by
  induction order generalizing s with
  | nil => exact measurable_const
  | cons x xs ih =>
    by_cases hx : x ∈ s.roots
    · simpa only [classicalExplore, if_pos hx] using ih s
    · have hb : Measurable (fun p : Option (State (V := V) (E := E) (I := I)) × (ℕ → Driver G) =>
          p.1.bind (fun t => classicalExplore G ι t xs p.2)) := by
        apply measurable_from_prod_countable_right
        intro o
        cases o with
        | none => exact measurable_const
        | some t => exact ih t
      simp only [classicalExplore, if_neg hx]
      exact hb.comp (((measurable_query G ι s x).comp (measurable_pi_apply 0)).prodMk
          (measurable_pi_lambda _ (fun i => measurable_pi_apply (i + 1))))

variable (μ : Measure (Letter G)) [IsProbabilityMeasure μ]

theorem query_tail_joint_law (s : State (V := V) (E := E) (I := I)) (x : V) :
    (driversLaw G μ).map (fun ω => (query G ι s x (ω 0), rowsAfter G 1 ω)) =
      ((driverLaw G μ).map (query G ι s x)).prod (driversLaw G μ) := by
  have hi : IndepFun (fun ω : ℕ → Driver G => ω 0) (rowsAfter G 1) (driversLaw G μ) :=
    (rowsBefore_indep_tail G μ 1).comp
      (measurable_pi_apply (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1)) measurable_id
  have hq := hi.comp (measurable_query G ι s x) measurable_id
  have ht : Measurable (rowsAfter G 1) := measurable_pi_lambda _ (fun i => measurable_pi_apply (1 + i))
  have hh := hq.map_prod_eq_prod_map_map
    ((measurable_query G ι s x).comp (measurable_pi_apply 0)).aemeasurable ht.aemeasurable
  simp only [Function.comp_apply] at hh
  rw [hh, rowsAfter_law]
  rw [← Measure.map_map (measurable_query G ι s x) (measurable_pi_apply 0)]
  rw [show (driversLaw G μ).map (fun ω => ω 0) = driverLaw G μ from Measure.infinitePi_map_eval _ 0]

omit [Nonempty (Letter G)] in
private theorem map_bind_prod_eq (ξ : Measure (Option (State (V := V) (E := E) (I := I))))
    (M M' : Measure (ℕ → Driver G)) [IsProbabilityMeasure M] [IsProbabilityMeasure M']
    (f g : State (V := V) (E := E) (I := I) → (ℕ → Driver G) → Option (State (V := V) (E := E) (I := I)))
    (hf : ∀ t, Measurable (f t)) (hg : ∀ t, Measurable (g t))
    (he : ∀ t, M.map (f t) = M'.map (g t)) :
    (ξ.prod M).map (fun p => p.1.bind (fun t => f t p.2)) =
      (ξ.prod M').map (fun p => p.1.bind (fun t => g t p.2)) := by
  have hmf : Measurable (fun p : Option (State (V := V) (E := E) (I := I)) × (ℕ → Driver G) =>
      p.1.bind (fun t => f t p.2)) := by
    apply measurable_from_prod_countable_right
    intro o; cases o with
    | none => exact measurable_const
    | some t => exact hf t
  have hmg : Measurable (fun p : Option (State (V := V) (E := E) (I := I)) × (ℕ → Driver G) =>
      p.1.bind (fun t => g t p.2)) := by
    apply measurable_from_prod_countable_right
    intro o; cases o with
    | none => exact measurable_const
    | some t => exact hg t
  ext U hU
  rw [Measure.map_apply hmf hU, Measure.map_apply hmg hU,
    Measure.prod_apply (hmf hU), Measure.prod_apply (hmg hU)]
  apply lintegral_congr
  intro o
  cases o with
  | none =>
    change M {ω | none ∈ U} = M' {ω | none ∈ U}
    by_cases hu : none ∈ U
    · simp [hu]
    · simp [hu]
  | some t =>
    have hs : (Prod.mk (some t) ⁻¹' (fun p => p.1.bind (fun t => f t p.2)) ⁻¹' U) = f t ⁻¹' U := by
      ext ω; rfl
    have hs' : (Prod.mk (some t) ⁻¹' (fun p => p.1.bind (fun t => g t p.2)) ⁻¹' U) = g t ⁻¹' U := by
      ext ω; rfl
    rw [hs, hs', ← Measure.map_apply (hf t) hU, ← Measure.map_apply (hg t) hU, he t]

theorem explorationLaw_eq_classical (s : State (V := V) (E := E) (I := I)) (order : List V) :
    explorationLaw G ι μ s order = (driversLaw G μ).map (classicalExplore G ι s order) := by
  induction order generalizing s with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x ∈ s.roots
    · have he : explore G ι s (x :: xs) = explore G ι s xs ∘ rowsAfter G 1 := by
        funext ω
        simp only [explore, query, if_pos hx, Option.bind_some, Function.comp_apply]
        congr 1
        funext i
        exact congrArg ω (Nat.add_comm i 1)
      rw [explorationLaw, he, ← Measure.map_map (measurable_explore G ι s xs)
        (measurable_pi_lambda _ (fun i => measurable_pi_apply (1 + i))), rowsAfter_law]
      simpa only [explorationLaw, classicalExplore, if_pos hx] using ih s
    · let b := fun p : Option (State (V := V) (E := E) (I := I)) × (ℕ → Driver G) =>
          p.1.bind (fun t => explore G ι t xs p.2)
      let c := fun p : Option (State (V := V) (E := E) (I := I)) × (ℕ → Driver G) =>
          p.1.bind (fun t => classicalExplore G ι t xs p.2)
      have hb : Measurable b := by
        apply measurable_from_prod_countable_right
        intro o; cases o with
        | none => exact measurable_const
        | some t => exact measurable_explore G ι t xs
      have hc : Measurable c := by
        apply measurable_from_prod_countable_right
        intro o; cases o with
        | none => exact measurable_const
        | some t => exact measurable_classicalExplore G ι t xs
      have hq : Measurable (fun ω : ℕ → Driver G => (query G ι s x (ω 0), rowsAfter G 1 ω)) :=
        ((measurable_query G ι s x).comp (measurable_pi_apply 0)).prodMk
          (measurable_pi_lambda _ (fun i => measurable_pi_apply (1 + i)))
      have he : explore G ι s (x :: xs) = b ∘ (fun ω => (query G ι s x (ω 0), rowsAfter G 1 ω)) := by
        funext ω
        simp only [explore, b, Function.comp_apply]
        rw [show (fun i => ω (i + 1)) = rowsAfter G 1 ω from
          funext (fun i => congrArg ω (Nat.add_comm i 1))]
      have he' : classicalExplore G ι s (x :: xs) = c ∘ (fun ω => (query G ι s x (ω 0), rowsAfter G 1 ω)) := by
        funext ω
        simp only [classicalExplore, if_neg hx, c, Function.comp_apply]
        rw [show (fun i => ω (i + 1)) = rowsAfter G 1 ω from
          funext (fun i => congrArg ω (Nat.add_comm i 1))]
      rw [explorationLaw, he, he', ← Measure.map_map hb hq, ← Measure.map_map hc hq, query_tail_joint_law]
      exact map_bind_prod_eq G _ _ _ _ _ (fun t => measurable_explore G ι t xs)
        (fun t => measurable_classicalExplore G ι t xs) (fun t => ih t)

variable [∀ v : V, MeasurableSpace (Incident G v)] [∀ v : V, MeasurableSingletonClass (Incident G v)]
variable (ν : Measure (Letter G)) [IsProbabilityMeasure ν]

theorem explorationLaw_eq_of_incident_marginals
    (h : ∀ v : V, μ.map (fun a => a v) = ν.map (fun a => a v))
    (s : State (V := V) (E := E) (I := I)) (order : List V) :
    explorationLaw G ι μ s order = explorationLaw G ι ν s order := by
  induction order generalizing s with
  | nil => simp [explorationLaw, explore]
  | cons x xs ih =>
    let b := fun p : Option (State (V := V) (E := E) (I := I)) × (ℕ → Driver G) =>
      p.1.bind (fun t => explore G ι t xs p.2)
    have hb : Measurable b := by
      apply measurable_from_prod_countable_right
      intro o; cases o with
      | none => exact measurable_const
      | some t => exact measurable_explore G ι t xs
    have hq : Measurable (fun ω : ℕ → Driver G => (query G ι s x (ω 0), rowsAfter G 1 ω)) :=
      ((measurable_query G ι s x).comp (measurable_pi_apply 0)).prodMk
        (measurable_pi_lambda _ (fun i => measurable_pi_apply (1 + i)))
    have he : explore G ι s (x :: xs) = b ∘ (fun ω => (query G ι s x (ω 0), rowsAfter G 1 ω)) := by
      funext ω
      simp only [explore, b, Function.comp_apply]
      rw [show (fun i => ω (i + 1)) = rowsAfter G 1 ω from
        funext (fun i => congrArg ω (Nat.add_comm i 1))]
    rw [explorationLaw, explorationLaw, he, ← Measure.map_map hb hq, ← Measure.map_map hb hq,
      query_tail_joint_law, query_tail_joint_law, query_law_eq G μ ν ι h]
    exact map_bind_prod_eq G _ _ _ _ _ (fun t => measurable_explore G ι t xs)
      (fun t => measurable_explore G ι t xs) (fun t => ih t)

end
end FiniteAvalanches.Wilson.CopiedNetwork
