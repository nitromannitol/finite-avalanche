import FiniteAvalanches.Sandpile.Recurrence.RawIntegerBox
import FiniteAvalanches.Sandpile.Components.TreeMass
import FiniteAvalanches.Sandpile.SourceCounting.CountingPaths

/-! Finite counting and the specified source embedding of raw integer sandpiles. -/
namespace FiniteAvalanches.Sandpile.RawInteger
open LatticeProb FiniteAvalanches.Sandpile MeasureTheory
open FiniteAvalanches.External.SandpileLimit
open FiniteAvalanches.Sandpile.SourceCounting
open scoped Classical ENNReal
noncomputable section

instance (Γ : Finset Site2) : MeasurableSpace (AllowedState Γ) := ⊤
instance (Γ : Finset Site2) : MeasurableSingletonClass (AllowedState Γ) := ⟨fun _ => trivial⟩

/-- Uniform counting on the full integer stable/noFSC carrier of the stated volume. -/
def integerAllowedLaw (Γ : Finset Site2) : Measure (AllowedState Γ) :=
  FiniteAvalanches.uniformMeasure (AllowedState Γ)

theorem integer_allowed_law_embedding (Γ : Finset Site2) :
    Measure.map (allowedEmbedding : AllowedState Γ → StableField) (integerAllowedLaw Γ) =
      finiteFieldLawOn Γ := by
  have h := congrArg (Measure.map (Subtype.val : allowedFields Γ → StableField))
    (FiniteAvalanches.uniform_measure_map_equiv (allowedFieldEquiv Γ))
  rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)] at h
  exact h

abbrev RecurrentState (N : ℕ) :=
  {η : StableState (boxSites N) // Accessible η.val}

def recurrentAllowedEquiv (N : ℕ) : RecurrentState N ≃ AllowedState (boxSites N) :=
  Equiv.subtypeEquivRight (fun η => (no_fsc_iff_accessible_box η).symm)

def sourceRecurrentEquiv (N : ℕ) : RecurrentState N ≃ FiniteWired.Recurrent N :=
  ((recurrentAllowedEquiv N).trans (allowedFieldEquiv (boxSites N))).trans (boxRecurrentEquiv N).symm

instance (N : ℕ) : Fintype (RecurrentState N) :=
  Fintype.ofEquiv _ (sourceRecurrentEquiv N).symm
instance (N : ℕ) : Nonempty (RecurrentState N) :=
  Nonempty.map (sourceRecurrentEquiv N).symm inferInstance
instance (N : ℕ) : MeasurableSpace (RecurrentState N) := ⊤
instance (N : ℕ) : MeasurableSingletonClass (RecurrentState N) := ⟨fun _ => trivial⟩

theorem source_recurrent_equiv_value {N : ℕ} (η : RecurrentState N)
    (x : FiniteWired.Active N) :
    (((sourceRecurrentEquiv N η).val x).val : ℤ) = η.val.val (boxVertex N x) := by
  have he : boxRecurrentEquiv N (sourceRecurrentEquiv N η) =
      allowedFieldEquiv (boxSites N) (recurrentAllowedEquiv N η) :=
    (boxRecurrentEquiv N).apply_symm_apply _
  have h := congrArg (fun ζ : allowedFields (boxSites N) => ((ζ.val (FiniteWired.site x)).val : ℤ)) he
  change ((FiniteWired.zeroExtend N (sourceRecurrentEquiv N η) (FiniteWired.site x)).val : ℤ) =
    ((allowedEmbedding (recurrentAllowedEquiv N η) (FiniteWired.site x)).val : ℤ) at h
  rw [FiniteWired.zeroExtend_site] at h
  exact h.trans (allowed_embedding_value (recurrentAllowedEquiv N η) (boxVertex N x))

theorem source_recurrent_equiv_unique {N : ℕ} (η : RecurrentState N)
    (ζ : FiniteWired.Recurrent N)
    (hζ : ∀ x, ((ζ.val x).val : ℤ) = η.val.val (boxVertex N x)) :
    ζ = sourceRecurrentEquiv N η := by
  apply Subtype.ext
  funext x
  apply Fin.ext
  exact_mod_cast (hζ x).trans (source_recurrent_equiv_value η x).symm

/-- The finite volume law uses exactly the already specified zero extension. -/
def sourceEmbedding (N : ℕ) (η : RecurrentState N) : StableField :=
  FiniteWired.zeroExtend N (sourceRecurrentEquiv N η)

theorem source_embedding_value {N : ℕ} (η : RecurrentState N) (x : FiniteWired.Active N) :
    ((sourceEmbedding N η (FiniteWired.site x)).val : ℤ) = η.val.val (boxVertex N x) := by
  rw [sourceEmbedding, FiniteWired.zeroExtend_site]
  exact source_recurrent_equiv_value η x

theorem source_embedding_unique {N : ℕ} (η : RecurrentState N) (f : StableField)
    (hi : ∀ x, ((f (FiniteWired.site x)).val : ℤ) = η.val.val (boxVertex N x))
    (ho : ∀ x, ¬FiniteWired.inBox N x → f x = 0) : f = sourceEmbedding N η := by
  funext x
  by_cases hx : FiniteWired.inBox N x
  · apply Fin.ext
    exact_mod_cast (hi (FiniteWired.activeOfSite N x hx)).trans
      (source_embedding_value η (FiniteWired.activeOfSite N x hx)).symm
  · exact (ho x hx).trans (FiniteWired.zeroExtend_outside N (sourceRecurrentEquiv N η) x hx).symm

def integerRecurrentLaw (N : ℕ) : Measure (RecurrentState N) :=
  FiniteAvalanches.uniformMeasure (RecurrentState N)

theorem integer_recurrent_law_embedding (N : ℕ) :
    Measure.map (sourceEmbedding N) (integerRecurrentLaw N) = FiniteWired.finiteFieldLaw N := by
  have h := congrArg (Measure.map (FiniteWired.zeroExtend N))
    (FiniteAvalanches.uniform_measure_map_equiv (sourceRecurrentEquiv N))
  rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)] at h
  have he : FiniteWired.law N = FiniteAvalanches.uniformMeasure (FiniteWired.Recurrent N) := by
    simp only [FiniteWired.law, FiniteAvalanches.uniformMeasure, Nat.card_eq_fintype_card]
  rw [FiniteWired.finiteFieldLaw, he]
  exact h

theorem card_integer_recurrent_eq_tree_count (N : ℕ) :
    Nat.card (RecurrentState N) = WiredTrees.treeCount N := by
  rw [Nat.card_congr (sourceRecurrentEquiv N), Nat.card_eq_fintype_card]
  exact FiniteAvalanches.Sandpile.Components.card_original_recurrent_eq_treeCount N

/-- All marks are represented before the actual finite counting event is formed. -/
theorem guarded_mark_zero_count {N r : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N) :
    integerRecurrentLaw N {η | ∀ x : sourceMarks r,
      η.val.val ⟨x.val, (mem_box_sites N x.val).mpr (sourceMarks_inBox hr hrN x.property)⟩ = 0} =
    (Nat.card {ζ : FiniteWired.Recurrent N // ∀ x : sourceMarks r,
      (ζ.val (FiniteWired.activeOfSite N x.val (sourceMarks_inBox hr hrN x.property))).val = 0} : ℝ≥0∞) /
      WiredTrees.treeCount N := by
  let P (η : RecurrentState N) : Prop := ∀ x : sourceMarks r,
    η.val.val ⟨x.val, (mem_box_sites N x.val).mpr (sourceMarks_inBox hr hrN x.property)⟩ = 0
  let Q (ζ : FiniteWired.Recurrent N) : Prop := ∀ x : sourceMarks r,
    (ζ.val (FiniteWired.activeOfSite N x.val (sourceMarks_inBox hr hrN x.property))).val = 0
  have he : ∀ η, P η ↔ Q (sourceRecurrentEquiv N η) := by
    intro η
    have hv : ∀ x : sourceMarks r,
        (((sourceRecurrentEquiv N η).val
          (FiniteWired.activeOfSite N x.val (sourceMarks_inBox hr hrN x.property))).val : ℤ) =
        η.val.val ⟨x.val, (mem_box_sites N x.val).mpr (sourceMarks_inBox hr hrN x.property)⟩ :=
      fun x => source_recurrent_equiv_value η _
    constructor <;> intro hh x
    · have hx := hh x
      have hvx := hv x
      change _ = 0
      omega
    · have hx := hh x
      have hvx := hv x
      change _ = 0
      omega
  have ec : {η : RecurrentState N // P η} ≃ {ζ : FiniteWired.Recurrent N // Q ζ} :=
    Equiv.subtypeEquiv (sourceRecurrentEquiv N) he
  rw [integerRecurrentLaw, FiniteAvalanches.uniformMeasure_apply,
    card_integer_recurrent_eq_tree_count]
  change (Nat.card {η : RecurrentState N // P η} : ℝ≥0∞) / WiredTrees.treeCount N =
    (Nat.card {ζ : FiniteWired.Recurrent N // Q ζ} : ℝ≥0∞) / WiredTrees.treeCount N
  rw [Nat.card_congr ec]

end
end FiniteAvalanches.Sandpile.RawInteger
