import FiniteAvalanches.Wilson.Markov

/-! A full unused IID-driver tail remains fresh after a literal finite copied
exploration. Every query slot is consumed, even when its start is already retained. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.CopiedNetwork
open MeasureTheory ProbabilityTheory MeasurableSpace FiniteAvalanches.Trees
open scoped Classical ENNReal
noncomputable section
variable {V E I : Type} [Fintype V] [Fintype E] [Countable I]
variable (G : Multigraph V E) (ι : E ↪ I) [Nonempty (Letter G)]

def prefixExplore (s : State (V := V) (E := E) (I := I)) :
    (order : List V) → (Fin order.length → Driver G) → Option (State (V := V) (E := E) (I := I))
  | [], _ => some s
  | x :: xs, ω => (query G ι s x (ω ⟨0, Nat.zero_lt_succ _⟩)).bind
      (fun t => prefixExplore t xs (fun i => ω ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩))

def rowsBefore (n : ℕ) (ω : ℕ → Driver G) : Fin n → Driver G := fun i => ω i
def rowsAfter (n : ℕ) (ω : ℕ → Driver G) : ℕ → Driver G := fun i => ω (n + i)

omit [Countable I] [Nonempty (Letter G)] in
theorem explore_eq_prefix (s : State (V := V) (E := E) (I := I)) (order : List V) (ω : ℕ → Driver G) :
    explore G ι s order ω = prefixExplore G ι s order (rowsBefore G order.length ω) := by
  induction order generalizing s ω with
  | nil => rfl
  | cons x xs ih =>
    simp only [explore, prefixExplore, rowsBefore]
    cases query G ι s x (ω 0) with
    | none => rfl
    | some t => exact ih t (fun i => ω (i + 1))

theorem measurable_prefixExplore (s : State (V := V) (E := E) (I := I)) (order : List V) :
    Measurable (prefixExplore G ι s order) := by
  induction order generalizing s with
  | nil => exact measurable_const
  | cons x xs ih =>
    have hb : Measurable (fun p : Option (State (V := V) (E := E) (I := I)) × (Fin xs.length → Driver G) =>
        p.1.bind (fun t => prefixExplore G ι t xs p.2)) := by
      apply measurable_from_prod_countable_right
      intro o
      cases o with
      | none => exact measurable_const
      | some t => exact ih t
    exact hb.comp (((measurable_query G ι s x).comp (measurable_pi_apply (⟨0, Nat.zero_lt_succ _⟩ : Fin (x :: xs).length))).prodMk
      (measurable_pi_lambda _ (fun i : Fin xs.length => measurable_pi_apply (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (x :: xs).length))))

variable (μ : Measure (Letter G)) [IsProbabilityMeasure μ]

instance driversLaw_probability : IsProbabilityMeasure (driversLaw G μ) := by unfold driversLaw; infer_instance

omit [Countable I] [Nonempty (Letter G)] in
theorem rowsAfter_law (n : ℕ) : (driversLaw G μ).map (rowsAfter G n) = driversLaw G μ :=
  Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => driverLaw G μ)
    (fun _ _ h => Nat.add_left_cancel h)

omit [Countable I] [Nonempty (Letter G)] in
theorem rowsBefore_indep_tail (n : ℕ) : IndepFun (rowsBefore G n) (rowsAfter G n) (driversLaw G μ) := by
  let m : ℕ → MeasurableSpace (ℕ → Driver G) := fun i =>
    (inferInstance : MeasurableSpace (Driver G)).comap (fun ω => ω i)
  have hm : ∀ i, m i ≤ (inferInstance : MeasurableSpace (ℕ → Driver G)) := fun i => (measurable_pi_apply i).comap_le
  have hi : iIndep m (driversLaw G μ) :=
    (iIndepFun_infinitePi (X := fun _ a => a) (P := fun _ : ℕ => driverLaw G μ) (fun _ => measurable_id)).iIndep
  have hd : Disjoint {i : ℕ | i < n} {i : ℕ | n ≤ i} :=
    Set.disjoint_left.mpr (fun i hi hj => Nat.not_lt_of_ge hj hi)
  have h := indep_iSup_of_disjoint hm hi hd
  change Indep ((inferInstance : MeasurableSpace (Fin n → Driver G)).comap (rowsBefore G n))
    ((inferInstance : MeasurableSpace (ℕ → Driver G)).comap (rowsAfter G n)) (driversLaw G μ)
  apply indep_of_indep_of_le h
  · rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    apply iSup_le
    intro i
    rw [MeasurableSpace.comap_comp]
    exact le_iSup₂_of_le i.val i.isLt le_rfl
  · rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    apply iSup_le
    intro i
    rw [MeasurableSpace.comap_comp]
    exact le_iSup₂_of_le (n + i) (Nat.le_add_right n i) le_rfl

theorem explore_indep_tail (s : State (V := V) (E := E) (I := I)) (order : List V) :
    IndepFun (explore G ι s order) (rowsAfter G order.length) (driversLaw G μ) := by
  have h := (rowsBefore_indep_tail G μ order.length).comp (measurable_prefixExplore G ι s order) measurable_id
  have he : explore G ι s order = prefixExplore G ι s order ∘ rowsBefore G order.length := by
    funext ω
    exact explore_eq_prefix G ι s order ω
  rw [he]
  exact h

/-- Full state and full unused rows factor, including null histories and failure. -/
theorem explore_tail_joint_law (s : State (V := V) (E := E) (I := I)) (order : List V) :
    (driversLaw G μ).map (fun ω => (explore G ι s order ω, rowsAfter G order.length ω)) =
      ((driversLaw G μ).map (explore G ι s order)).prod (driversLaw G μ) := by
  have hm : Measurable (rowsAfter G order.length) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply (order.length + i))
  rw [(explore_indep_tail G ι μ s order).map_prod_eq_prod_map_map
    (measurable_explore G ι s order).aemeasurable hm.aemeasurable, rowsAfter_law]

end
end FiniteAvalanches.Wilson.CopiedNetwork
