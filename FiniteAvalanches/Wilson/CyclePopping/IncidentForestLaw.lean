import FiniteAvalanches.Wilson.CyclePopping.IncidentForestEquiv

/-! Uniform cycle-popping forests on finite copied-edge graphs. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open FiniteAvalanches.Trees MeasureTheory ProbabilityTheory Function
open scoped Classical ENNReal

noncomputable section

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
variable (G : Multigraph V E) [∀ v, Nonempty (IncidentCopy G v)]

instance incidentCopyMeasurableSpace (v : V) : MeasurableSpace (IncidentCopy G v) := ⊤
instance incidentCopyMeasurableSingletonClass (v : V) :
    MeasurableSingletonClass (IncidentCopy G v) := ⟨fun _ => trivial⟩

/-- Stack configurations whose terminal arrows select a given copied forest. -/
def incidentStackForestEvent (R : Set V) (k : Cursor V) (F : G.RootedForest R) :
    Set ((p : V × ℕ) → IncidentCopy G p.1) :=
  {σ | ∃ a : GoodIncidentArrows G R,
    incidentArrowForest G R a = F ∧
    σ ∈ terminalOutputEvent R (incidentCopyHead G) k (fun v i σ => σ (v, i)) a}

/-- Terminal assignments selecting a forest differ only at roots. -/
theorem incidentStackForestEvent_eq_iUnion (R : Set V) (k : Cursor V) (F : G.RootedForest R) :
    incidentStackForestEvent G R k F = ⋃ d : IncidentRootCopies G R,
      terminalOutputEvent R (incidentCopyHead G) k (fun v i σ => σ (v, i))
        (forestIncidentArrowsWithRoots G R F d) := by
  ext σ
  simp only [incidentStackForestEvent, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨a, ha, hσ⟩
    refine ⟨fun r => a.val r.val, ?_⟩
    have he : forestIncidentArrowsWithRoots G R F (fun r => a.val r.val) = a := by
      have h := (incidentArrowForestEquiv G R).left_inv a
      change forestIncidentArrowsWithRoots G R (incidentArrowForest G R a)
        (fun r => a.val r.val) = a at h
      rwa [ha] at h
    rw [he]
    exact hσ
  · rintro ⟨d, hd⟩
    exact ⟨forestIncidentArrowsWithRoots G R F d,
      incidentArrowForest_forestIncidentArrowsWithRoots G R F d, hd⟩

/-- The terminal forest selected by independent uniform incident stacks is
uniform among the original-copy rooted forests. -/
theorem variableStackLaw_incidentForest_uniform (R : Set V) (k : Cursor V)
    (F : G.RootedForest R) :
    variableStackLaw (IncidentCopy G) (incidentStackForestEvent G R k F) =
      1 / (Fintype.card (G.RootedForest R) : ℝ≥0∞) := by
  let Q : IncidentRootCopies G R → Set ((p : V × ℕ) → IncidentCopy G p.1) :=
    fun d => terminalOutputEvent R (incidentCopyHead G) k (fun v i σ => σ (v, i))
      (forestIncidentArrowsWithRoots G R F d)
  have hinj : Function.Injective (forestIncidentArrowsWithRoots G R F) := by
    intro d e hde
    have h := congrArg (fun a => (incidentArrowForestEquiv G R a).2) hde
    have hd := (incidentArrowForestEquiv G R).right_inv (F, d)
    have he := (incidentArrowForestEquiv G R).right_inv (F, e)
    exact (congrArg Prod.snd hd).symm.trans (h.trans (congrArg Prod.snd he))
  have hdis : Pairwise (Disjoint on Q) := by
    intro d e hde
    exact disjoint_terminalOutputEvent R (incidentCopyHead G) k
      (fun v i (σ : (p : V × ℕ) → IncidentCopy G p.1) => σ (v, i))
      (fun h => hde (hinj h))
  have hmeas : ∀ d, MeasurableSet (Q d) := by
    intro d
    apply measurableSet_terminalOutputEvent
    intro v i
    exact measurable_pi_apply (v, i)
  have hunion : incidentStackForestEvent G R k F = ⋃ d, Q d :=
    incidentStackForestEvent_eq_iUnion G R k F
  rw [hunion, measure_iUnion hdis hmeas, tsum_fintype]
  simp_rw [show ∀ d, variableStackLaw (IncidentCopy G) (Q d) =
      1 / (Fintype.card (GoodIncidentArrows G R) : ℝ≥0∞) from
    fun d => variableStackLaw_terminal_uniform (IncidentCopy G) R (incidentCopyHead G) k
      (forestIncidentArrowsWithRoots G R F d)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : Fintype.card (GoodIncidentArrows G R) =
      Fintype.card (G.RootedForest R) * Fintype.card (IncidentRootCopies G R) := by
    rw [Fintype.card_congr (incidentArrowForestEquiv G R), Fintype.card_prod]
  rw [hcard, Nat.cast_mul]
  letI : Nonempty (IncidentRootCopies G R) := ⟨fun v => Classical.choice (inferInstance :
    Nonempty (IncidentCopy G v.val))⟩
  have hne : (Fintype.card (IncidentRootCopies G R) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have htop : (Fintype.card (IncidentRootCopies G R) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc
    (Fintype.card (IncidentRootCopies G R) : ℝ≥0∞) *
        (1 / ((Fintype.card (G.RootedForest R) : ℝ≥0∞) *
          (Fintype.card (IncidentRootCopies G R) : ℝ≥0∞))) =
      (1 * (Fintype.card (IncidentRootCopies G R) : ℝ≥0∞)) /
        ((Fintype.card (G.RootedForest R) : ℝ≥0∞) *
          (Fintype.card (IncidentRootCopies G R) : ℝ≥0∞)) := by
            simp only [one_mul, div_eq_mul_inv]
    _ = 1 / (Fintype.card (G.RootedForest R) : ℝ≥0∞) :=
      ENNReal.mul_div_mul_right 1 _ hne htop

/-- Terminal copied-forest events are measurable. -/
theorem measurableSet_incidentStackForestEvent (R : Set V) (k : Cursor V)
    (F : G.RootedForest R) : MeasurableSet (incidentStackForestEvent G R k F) := by
  rw [incidentStackForestEvent_eq_iUnion G R k F]
  apply MeasurableSet.iUnion
  intro d
  apply measurableSet_terminalOutputEvent
  intro v i
  exact measurable_pi_apply (v, i)

omit [∀ v, Nonempty (IncidentCopy G v)] in
/-- Different copied forests give disjoint terminal stack events. -/
theorem disjoint_incidentStackForestEvent (R : Set V) (k : Cursor V) :
    Pairwise (Disjoint on incidentStackForestEvent G R k) := by
  intro F H hne
  apply Set.disjoint_left.mpr
  intro σ hF hH
  obtain ⟨a, ha, hσa⟩ := hF
  obtain ⟨b, hb, hσb⟩ := hH
  by_cases hab : a = b
  · subst b
    exact hne (ha.symm.trans hb)
  · exact Set.disjoint_left.mp
      (disjoint_terminalOutputEvent R (incidentCopyHead G) k
        (fun v i (σ : (p : V × ℕ) → IncidentCopy G p.1) => σ (v, i)) hab) hσa hσb

/-- The terminal forest event has its exact uniform counting probability. -/
theorem variableStackLaw_incidentForestEvent_eq (R : Set V) (k : Cursor V)
    (S : Set (G.RootedForest R)) :
    variableStackLaw (IncidentCopy G)
      {σ | ∃ a : GoodIncidentArrows G R,
        incidentArrowForest G R a ∈ S ∧
        σ ∈ terminalOutputEvent R (incidentCopyHead G) k (fun v i σ => σ (v, i)) a} =
      (Nat.card S : ℝ≥0∞) / (Fintype.card (G.RootedForest R) : ℝ≥0∞) := by
  have he : {σ : (p : V × ℕ) → IncidentCopy G p.1 | ∃ a : GoodIncidentArrows G R,
        incidentArrowForest G R a ∈ S ∧
        σ ∈ terminalOutputEvent R (incidentCopyHead G) k (fun v i σ => σ (v, i)) a} =
      ⋃ F : S, incidentStackForestEvent G R k F.val := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, incidentStackForestEvent]
    constructor
    · rintro ⟨a, ha, hσ⟩
      exact ⟨⟨incidentArrowForest G R a, ha⟩, a, rfl, hσ⟩
    · rintro ⟨⟨F, hF⟩, a, ha, hσ⟩
      exact ⟨a, ha.symm ▸ hF, hσ⟩
  have hdis : Pairwise (Disjoint on fun F : S => incidentStackForestEvent G R k F.val) := by
    intro F H hne
    apply disjoint_incidentStackForestEvent G R k
    intro heq
    exact hne (Subtype.ext heq)
  rw [he, measure_iUnion hdis (fun F => measurableSet_incidentStackForestEvent G R k F.val),
    tsum_fintype]
  simp_rw [variableStackLaw_incidentForest_uniform G R k]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card,
    one_mul, div_eq_mul_inv]

end
end FiniteAvalanches.Wilson.CyclePopping
