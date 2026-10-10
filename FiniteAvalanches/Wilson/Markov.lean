import FiniteAvalanches.Wilson.Measurability
import Mathlib.Probability.Kernel.Basic

/-! Integrated Markov transitions derived from IID legal-copy letters. No
positive-history ratio or independence assumption is supplied by the caller. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.CopiedNetwork
open MeasureTheory ProbabilityTheory MeasurableSpace FiniteAvalanches.Trees
open scoped Classical ENNReal
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)
variable [MeasurableSpace V] [MeasurableSingletonClass V]
variable (μ : Measure (Letter G)) [IsProbabilityMeasure μ]

def driverLaw : Measure (Driver G) := Measure.infinitePi (fun _ : ℕ => μ)
instance driverLaw_probability : IsProbabilityMeasure (driverLaw G μ) := by unfold driverLaw; infer_instance

def letterKernel : Kernel V V where
  toFun v := μ.map (fun a => other G v (a v))
  measurable' := measurable_of_countable _

instance letterKernel_markov : IsMarkovKernel (letterKernel G μ) where
  isProbabilityMeasure _ := Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

abbrev pastSpace (n : ℕ) : MeasurableSpace (Driver G) :=
  ⨆ k ∈ {k : ℕ | k < n}, (inferInstance : MeasurableSpace (Letter G)).comap (fun ω => ω k)

private theorem measurable_position_of_eval (x : V) (n : ℕ) (m : MeasurableSpace (Driver G))
    (h : ∀ k < n, @Measurable _ _ m (inferInstance : MeasurableSpace (Letter G)) (fun ω => ω k)) :
    @Measurable _ _ m (inferInstance : MeasurableSpace V) (fun ω => position G x ω n) := by
  letI := m
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (measurable_of_countable (fun p : V × Letter G => other G p.1 (p.2 p.1))).comp
      ((ih (fun k hk => h k (Nat.lt_succ_of_lt hk))).prodMk (h n (Nat.lt_succ_self n)))

theorem measurable_position_past (x : V) (n : ℕ) :
    @Measurable _ _ (pastSpace G n) (inferInstance : MeasurableSpace V) (fun ω => position G x ω n) := by
  apply measurable_position_of_eval
  intro k hk
  exact measurable_iff_comap_le.mpr (le_iSup₂_of_le k hk le_rfl)

omit [MeasurableSpace V] [MeasurableSingletonClass V] in
theorem past_indep_next (n : ℕ) :
    Indep (pastSpace G n) ((inferInstance : MeasurableSpace (Letter G)).comap
      (fun ω : Driver G => ω n)) (driverLaw G μ) := by
  let m : ℕ → MeasurableSpace (Driver G) := fun i =>
    (inferInstance : MeasurableSpace (Letter G)).comap (fun ω => ω i)
  have hm : ∀ i, m i ≤ (inferInstance : MeasurableSpace (Driver G)) := fun i => (measurable_pi_apply i).comap_le
  have hi : iIndepFun (fun i (ω : Driver G) => ω i) (driverLaw G μ) :=
    iIndepFun_infinitePi (X := fun _ a => a) (fun _ => measurable_id)
  have hd : Disjoint {i : ℕ | i < n} {n} := Set.disjoint_singleton_right.mpr (Nat.lt_irrefl n)
  have h := indep_iSup_of_disjoint hm hi.iIndep hd
  simpa only [pastSpace, Set.mem_singleton_iff, iSup_iSup_eq_left] using h

private theorem fixed_step_law (n : ℕ) (v : V) (U : Set V) :
    driverLaw G μ {ω | other G v (ω n v) ∈ U} = letterKernel G μ v U := by
  have hU := (Set.to_countable U).measurableSet
  calc
    _ = ((driverLaw G μ).map (fun ω => ω n)) ((fun a => other G v (a v)) ⁻¹' U) :=
      (Measure.map_apply (measurable_pi_apply n) ((measurable_of_countable _) hU)).symm
    _ = letterKernel G μ v U := by
      rw [show (driverLaw G μ).map (fun ω => ω n) = μ from Measure.infinitePi_map_eval _ n]
      exact (Measure.map_apply (measurable_of_countable (fun a : Letter G => other G v (a v))) hU).symm

theorem transition_given_past (x : V) (n : ℕ) (H : Set (Driver G))
    (hH : MeasurableSet[pastSpace G n] H) (v : V) (U : Set V) :
    driverLaw G μ {ω | ω ∈ H ∧ position G x ω n = v ∧ position G x ω (n + 1) ∈ U} =
      driverLaw G μ {ω | ω ∈ H ∧ position G x ω n = v} * letterKernel G μ v U := by
  let A : Set (Driver G) := {ω | ω ∈ H ∧ position G x ω n = v}
  let B : Set (Driver G) := {ω | other G v (ω n v) ∈ U}
  have hA : MeasurableSet[pastSpace G n] A :=
    hH.inter ((measurable_position_past G x n) (measurableSet_singleton v))
  have hU := (Set.to_countable U).measurableSet
  have hev : @Measurable _ _ ((inferInstance : MeasurableSpace (Letter G)).comap
      (fun ω : Driver G => ω n)) (inferInstance : MeasurableSpace (Letter G)) (fun ω : Driver G => ω n) :=
    measurable_iff_comap_le.mpr le_rfl
  have hB : MeasurableSet[(inferInstance : MeasurableSpace (Letter G)).comap
      (fun ω : Driver G => ω n)] B :=
    ((measurable_of_countable (fun a : Letter G => other G v (a v))) hU).preimage hev
  have hi := (Indep_iff _ _ _).mp (past_indep_next G μ n) A B hA hB
  have he : {ω : Driver G | ω ∈ H ∧ position G x ω n = v ∧ position G x ω (n + 1) ∈ U} = A ∩ B := by
    ext ω
    simp only [A, B, Set.mem_inter_iff, Set.mem_setOf_eq, position]
    constructor
    · rintro ⟨hH, hv, hU⟩
      subst v
      exact ⟨⟨hH, rfl⟩, hU⟩
    · rintro ⟨⟨hH, hv⟩, hU⟩
      subst v
      exact ⟨hH, rfl, hU⟩
  rw [he, hi]
  change _ = _
  rw [fixed_step_law]

end
end FiniteAvalanches.Wilson.CopiedNetwork
