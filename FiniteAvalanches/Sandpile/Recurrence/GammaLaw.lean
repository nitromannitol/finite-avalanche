import FiniteAvalanches.Sandpile.Recurrence.GammaAccessibility

/-! Uniform finite-volume counting on actual ALL-input accessible integer states.
The Fin 4 embedding is characterized uniquely by its heights and zero exterior. -/
namespace FiniteAvalanches.Sandpile.RawInteger
open LatticeProb FiniteAvalanches.Sandpile MeasureTheory
open FiniteAvalanches.External.SandpileLimit
open scoped Classical ENNReal
noncomputable section

abbrev GammaRecurrentState (Γ : Finset Site2) := {η : StableState Γ // Accessible η.val}

def gammaRecurrentAllowedEquiv (Γ : Finset Site2) : GammaRecurrentState Γ ≃ AllowedState Γ :=
  Equiv.subtypeEquivRight (fun η => (no_fsc_iff_accessible η.val).symm)

def gammaRecurrentFieldEquiv (Γ : Finset Site2) : GammaRecurrentState Γ ≃ allowedFields Γ :=
  (gammaRecurrentAllowedEquiv Γ).trans (allowedFieldEquiv Γ)

instance (Γ : Finset Site2) : Fintype (GammaRecurrentState Γ) :=
  Fintype.ofEquiv _ (gammaRecurrentFieldEquiv Γ).symm
instance (Γ : Finset Site2) : Nonempty (GammaRecurrentState Γ) :=
  Nonempty.map (gammaRecurrentFieldEquiv Γ).symm inferInstance
instance (Γ : Finset Site2) : MeasurableSpace (GammaRecurrentState Γ) := ⊤
instance (Γ : Finset Site2) : MeasurableSingletonClass (GammaRecurrentState Γ) := ⟨fun _ => trivial⟩

def gammaSourceEmbedding (Γ : Finset Site2) (η : GammaRecurrentState Γ) : StableField :=
  (gammaRecurrentFieldEquiv Γ η).val

theorem gamma_source_embedding_value {Γ : Finset Site2} (η : GammaRecurrentState Γ) (x : Γ) :
    ((gammaSourceEmbedding Γ η x.val).val : ℤ) = η.val.val x :=
  allowed_embedding_value (gammaRecurrentAllowedEquiv Γ η) x

theorem gamma_source_embedding_outside {Γ : Finset Site2} (η : GammaRecurrentState Γ)
    (x : Site2) (hx : x ∉ Γ) : gammaSourceEmbedding Γ η x = 0 :=
  (gammaRecurrentFieldEquiv Γ η).property.1 x hx

theorem gamma_source_embedding_unique {Γ : Finset Site2} (η : GammaRecurrentState Γ)
    (f : StableField) (hi : ∀ x : Γ, ((f x.val).val : ℤ) = η.val.val x)
    (ho : ∀ x, x ∉ Γ → f x = 0) : f = gammaSourceEmbedding Γ η := by
  funext x
  by_cases hx : x ∈ Γ
  · apply Fin.ext
    exact_mod_cast (hi ⟨x, hx⟩).trans (gamma_source_embedding_value η ⟨x, hx⟩).symm
  · exact (ho x hx).trans (gamma_source_embedding_outside η x hx).symm

def gammaIntegerRecurrentLaw (Γ : Finset Site2) : Measure (GammaRecurrentState Γ) :=
  FiniteAvalanches.uniformMeasure (GammaRecurrentState Γ)

/-- The actual source-accessible carrier pushes to the specified finite source law. -/
theorem gamma_integer_recurrent_law_embedding (Γ : Finset Site2) :
    Measure.map (gammaSourceEmbedding Γ) (gammaIntegerRecurrentLaw Γ) = finiteFieldLawOn Γ := by
  have h := congrArg (Measure.map (Subtype.val : allowedFields Γ → StableField))
    (FiniteAvalanches.uniform_measure_map_equiv (gammaRecurrentFieldEquiv Γ))
  rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)] at h
  exact h

/-- Exact event counting retains the whole raw recurrent carrier, including empty Gamma. -/
theorem gamma_recurrent_event_count (Γ : Finset Site2) (P : GammaRecurrentState Γ → Prop) :
    gammaIntegerRecurrentLaw Γ {η | P η} =
      (Nat.card {η : GammaRecurrentState Γ // P η} : ℝ≥0∞) / Nat.card (GammaRecurrentState Γ) :=
  FiniteAvalanches.uniformMeasure_apply _ _

end
end FiniteAvalanches.Sandpile.RawInteger
