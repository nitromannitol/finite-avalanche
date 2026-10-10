import FiniteAvalanches.Wilson.Markov

/-! A copied walk sees one vertex coordinate of each fresh letter. Consequently
its complete finite copied prefixes depend only on the incident-copy marginals,
even when coordinates within one letter are correlated. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.CopiedNetwork
open MeasureTheory ProbabilityTheory MeasurableSpace FiniteAvalanches.Trees
open scoped Classical ENNReal
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)

/-- Terminal and ordered destination/copy data. This record type is not a legal-path
carrier; actual walk records are compared with genuine endpoint-indexed paths below. -/
def PrefixRecord := V × List (V × E)

instance prefixRecordCountable : Countable (PrefixRecord (V := V) (E := E)) :=
  inferInstanceAs (Countable (V × List (V × E)))
instance prefixRecordMeasurableSpace : MeasurableSpace (PrefixRecord (V := V) (E := E)) := ⊤
instance prefixRecordMeasurableSingletonClass : MeasurableSingletonClass (PrefixRecord (V := V) (E := E)) :=
  ⟨fun _ => trivial⟩

def prefixStep (p : PrefixRecord (V := V) (E := E)) (a : Letter G) : PrefixRecord (V := V) (E := E) :=
  let e := a p.1
  let w := other G p.1 e
  (w, p.2 ++ [(w, e.val)])

def walkPrefix (x : V) (ω : Driver G) : ℕ → PrefixRecord (V := V) (E := E)
  | 0 => (x, [])
  | n + 1 => prefixStep G (walkPrefix x ω n) (ω n)

theorem walkPrefix_terminal (x : V) (ω : Driver G) (n : ℕ) :
    (walkPrefix G x ω n).1 = position G x ω n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only [walkPrefix, prefixStep, position]
    rw [ih]

private theorem measurable_walkPrefix_of_eval (x : V) (n : ℕ) (m : MeasurableSpace (Driver G))
    (h : ∀ k < n, @Measurable _ _ m (inferInstance : MeasurableSpace (Letter G)) (fun ω => ω k)) :
    @Measurable _ _ m (inferInstance : MeasurableSpace (PrefixRecord (V := V) (E := E)))
      (fun ω => walkPrefix G x ω n) := by
  letI := m
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (measurable_of_countable (fun p : PrefixRecord (V := V) (E := E) × Letter G => prefixStep G p.1 p.2)).comp
      ((ih (fun k hk => h k (Nat.lt_succ_of_lt hk))).prodMk (h n (Nat.lt_succ_self n)))

theorem measurable_walkPrefix (x : V) (n : ℕ) : Measurable (fun ω => walkPrefix G x ω n) :=
  measurable_walkPrefix_of_eval G x n _ (fun _ _ => measurable_pi_apply _)

theorem measurable_walkPrefix_past (x : V) (n : ℕ) :
    @Measurable _ _ (pastSpace G n) (inferInstance : MeasurableSpace (PrefixRecord (V := V) (E := E)))
      (fun ω => walkPrefix G x ω n) := by
  apply measurable_walkPrefix_of_eval
  intro k hk
  exact measurable_iff_comap_le.mpr (le_iSup₂_of_le k hk le_rfl)

variable (μ ν : Measure (Letter G)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem walkPrefix_indep_next (x : V) (n : ℕ) :
    IndepFun (fun ω => walkPrefix G x ω n) (fun ω : Driver G => ω n) (driverLaw G μ) :=
  indep_of_indep_of_le (past_indep_next G μ n) (measurable_walkPrefix_past G x n).comap_le le_rfl

theorem walkPrefix_joint_law (x : V) (n : ℕ) :
    (driverLaw G μ).map (fun ω => (walkPrefix G x ω n, ω n)) =
      ((driverLaw G μ).map (fun ω => walkPrefix G x ω n)).prod μ := by
  rw [(walkPrefix_indep_next G μ x n).map_prod_eq_prod_map_map
    (measurable_walkPrefix G x n).aemeasurable (measurable_pi_apply n).aemeasurable]
  rw [show (driverLaw G μ).map (fun ω => ω n) = μ from Measure.infinitePi_map_eval _ n]

variable [∀ v : V, MeasurableSpace (Incident G v)] [∀ v : V, MeasurableSingletonClass (Incident G v)]

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
/-- Identical incident-copy marginals suffice; equality of whole letter laws is unnecessary. -/
theorem prefixStep_law_eq (h : ∀ v : V, μ.map (fun a => a v) = ν.map (fun a => a v))
    (p : PrefixRecord (V := V) (E := E)) :
    μ.map (prefixStep G p) = ν.map (prefixStep G p) := by
  let f : Incident G p.1 → PrefixRecord (V := V) (E := E) :=
    fun e => (other G p.1 e, p.2 ++ [(other G p.1 e, e.val)])
  have hf : Measurable f := measurable_of_countable _
  calc
    _ = (μ.map (fun a => a p.1)).map f := (Measure.map_map hf (measurable_of_countable _)).symm
    _ = (ν.map (fun a => a p.1)).map f := by rw [h p.1]
    _ = _ := Measure.map_map hf (measurable_of_countable _)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem prefixStep_prod_law_eq (h : ∀ v : V, μ.map (fun a => a v) = ν.map (fun a => a v))
    (ξ : Measure (PrefixRecord (V := V) (E := E))) [SFinite μ] [SFinite ν] :
    (ξ.prod μ).map (fun p => prefixStep G p.1 p.2) =
      (ξ.prod ν).map (fun p => prefixStep G p.1 p.2) := by
  have hm : Measurable (fun p : PrefixRecord (V := V) (E := E) × Letter G => prefixStep G p.1 p.2) :=
    measurable_of_countable _
  ext U hU
  rw [Measure.map_apply hm hU, Measure.map_apply hm hU, Measure.prod_apply (hm hU), Measure.prod_apply (hm hU)]
  apply lintegral_congr
  intro p
  have he := congrArg (fun m : Measure (PrefixRecord (V := V) (E := E)) => m U)
    (prefixStep_law_eq G μ ν h p)
  have hs : Prod.mk p ⁻¹' (fun p : PrefixRecord (V := V) (E := E) × Letter G => prefixStep G p.1 p.2) ⁻¹' U =
      prefixStep G p ⁻¹' U := by ext a; rfl
  rw [hs]
  simpa only [Measure.map_apply (measurable_of_countable (prefixStep G p)) hU] using he

theorem walkPrefix_law_eq (h : ∀ v : V, μ.map (fun a => a v) = ν.map (fun a => a v))
    (x : V) (n : ℕ) :
    (driverLaw G μ).map (fun ω => walkPrefix G x ω n) =
      (driverLaw G ν).map (fun ω => walkPrefix G x ω n) := by
  induction n with
  | zero => simp [walkPrefix]
  | succ n ih =>
    have hm : Measurable (fun p : PrefixRecord (V := V) (E := E) × Letter G => prefixStep G p.1 p.2) :=
      measurable_of_countable _
    calc
      _ = ((driverLaw G μ).map (fun ω => (walkPrefix G x ω n, ω n))).map
          (fun p => prefixStep G p.1 p.2) :=
        (Measure.map_map hm ((measurable_walkPrefix G x n).prodMk (measurable_pi_apply n))).symm
      _ = (((driverLaw G μ).map (fun ω => walkPrefix G x ω n)).prod μ).map
          (fun p => prefixStep G p.1 p.2) := by rw [walkPrefix_joint_law]
      _ = (((driverLaw G ν).map (fun ω => walkPrefix G x ω n)).prod ν).map
          (fun p => prefixStep G p.1 p.2) := by rw [ih]; exact prefixStep_prod_law_eq G μ ν h _
      _ = ((driverLaw G ν).map (fun ω => (walkPrefix G x ω n, ω n))).map
          (fun p => prefixStep G p.1 p.2) := by rw [walkPrefix_joint_law]
      _ = _ := Measure.map_map hm ((measurable_walkPrefix G x n).prodMk (measurable_pi_apply n))

end
end FiniteAvalanches.Wilson.CopiedNetwork
