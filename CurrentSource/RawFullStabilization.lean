import FiniteAvalanches.Sandpile.Observables

/-! Legal stabilization on integer fields uses only upper stability. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Sandpile.RawFull
open LatticeProb LatticeProb.Sandpile FiniteAvalanches Sandpile
open scoped Classical
noncomputable section

abbrev Field := Site2 → ℤ

/-- Integer source stability imposes only the original degree upper bound. -/
def Stable (η : Field) : Prop := ∀ x, η x < 4

abbrev SourceState := {η : Field // Stable η}

def initial (η : Field) (ξ : Counts) (x : Site2) : ℤ := η x + (ξ x : ℤ)

/-- A finite actual legal word ending at an upper-stable integer field. -/
def Stabilizes (η : Field) (ξ : Counts) (w : List Site2) : Prop :=
  LegalList (initial η ξ) w ∧
    ∀ x, initial η ξ x + lap (fun y => (listCounts w y : ℤ)) x < 4

/-- First excess firing contradicts the candidate's upper stability; no lower
bound on the starting or terminal integer field is used. -/
theorem legal_prefix_le {s : Field} {w : List Site2} (h : LegalList s w)
    (v : Counts) (hv : ∀ x, s x + lap (fun y => (v y : ℤ)) x < 4) :
    ∀ k x, prefixCounts w k x ≤ (v x : ℤ) := by
  intro k
  induction k with
  | zero => intro x; rw [prefix_zero]; exact Nat.cast_nonneg _
  | succ k ih =>
    intro x
    rcases h.isLegalToppling.2 k x with he | ⟨he, htop⟩
    · rw [he]; exact ih x
    · rw [he]
      by_contra hlt
      have hx : prefixCounts w k x = (v x : ℤ) := le_antisymm (ih x) (by omega)
      have hl := lap_le_lap_of_le ih hx
      have hs := hv x
      norm_num at htop
      omega

theorem legal_counts_le {s : Field} {w : List Site2} (h : LegalList s w)
    (v : Counts) (hv : ∀ x, s x + lap (fun y => (v y : ℤ)) x < 4) :
    ∀ x, listCounts w x ≤ v x := by
  intro x
  have hp := legal_prefix_le h v hv w.length x
  rw [prefix_eq_terminal w w.length le_rfl] at hp
  change (listCounts w x : ℤ) ≤ (v x : ℤ) at hp
  exact_mod_cast hp

theorem stabilizes_counts_unique {η : Field} {ξ : Counts} {w v : List Site2}
    (hw : Stabilizes η ξ w) (hv : Stabilizes η ξ v) : listCounts w = listCounts v := by
  apply Finsupp.ext
  intro x
  exact le_antisymm (legal_counts_le hw.1 (listCounts v) hv.2 x)
    (legal_counts_le hv.1 (listCounts w) hw.2 x)

theorem existsUnique_counts {η : Field} {ξ : Counts}
    (h : ∃ w, Stabilizes η ξ w) :
    ∃! u : Counts, ∃ w, Stabilizes η ξ w ∧ listCounts w = u := by
  obtain ⟨w, hw⟩ := h
  refine ⟨listCounts w, ⟨w, hw, rfl⟩, ?_⟩
  rintro u ⟨v, hv, rfl⟩
  exact stabilizes_counts_unique hv hw

abbrev StabilizationDomain (ξ : Counts) := {η : Field // ∃ w, Stabilizes η ξ w}

/-- The unique count is defined only on the proved finite stabilization domain. -/
def odometer (ξ : Counts) (η : StabilizationDomain ξ) : Counts :=
  (existsUnique_counts η.property).choose

theorem odometer_spec (ξ : Counts) (η : StabilizationDomain ξ) :
    ∃ w, Stabilizes η.val ξ w ∧ listCounts w = odometer ξ η :=
  (existsUnique_counts η.property).choose_spec.1

theorem odometer_eq_counts (ξ : Counts) (η : StabilizationDomain ξ)
    {w : List Site2} (hw : Stabilizes η.val ξ w) : odometer ξ η = listCounts w := by
  obtain ⟨v, hv, he⟩ := odometer_spec ξ η
  exact he.symm.trans (stabilizes_counts_unique hv hw)

theorem odometer_full_characterization (ξ : Counts) (η : StabilizationDomain ξ) (u : Counts) :
    odometer ξ η = u ↔ ∃ w, Stabilizes η.val ξ w ∧ listCounts w = u := by
  constructor
  · intro h
    simpa only [h] using odometer_spec ξ η
  · rintro ⟨w, hw, rfl⟩
    exact odometer_eq_counts ξ η hw

theorem odometer_terminal_upper_stable (ξ : Counts) (η : StabilizationDomain ξ) :
    ∀ x, initial η.val ξ x + lap (fun y => (odometer ξ η y : ℤ)) x < 4 := by
  obtain ⟨w, hw, he⟩ := odometer_spec ξ η
  rw [← he]
  exact hw.2

def nnEmbedding (η : Sandpile.StableField) : SourceState :=
  ⟨fun x => ((η x).val : ℤ), fun x => by
    change ((η x).val : ℤ) < 4
    exact_mod_cast (η x).isLt⟩

theorem nnEmbedding_injective : Function.Injective nnEmbedding := by
  intro η ζ h
  funext x
  apply Fin.ext
  have he := congrFun (congrArg Subtype.val h) x
  change ((η x).val : ℤ) = ((ζ x).val : ℤ) at he
  exact_mod_cast he

def Nonnegative (η : SourceState) : Prop := ∀ x, 0 ≤ η.val x

/-- Encoding requires an actual nonnegativity proof; there is no invalid-state branch. -/
def nnEncoding (η : SourceState) (h : Nonnegative η) : Sandpile.StableField := fun x =>
  ⟨(η.val x).toNat, by have hl := h x; have hu := η.property x; omega⟩

theorem nnEmbedding_nnEncoding (η : SourceState) (h : Nonnegative η) :
    nnEmbedding (nnEncoding η h) = η := by
  apply Subtype.ext
  funext x
  exact Int.toNat_of_nonneg (h x)

theorem existsUnique_nn_encoding (η : SourceState) :
    (∃! ζ : Sandpile.StableField, nnEmbedding ζ = η) ↔ Nonnegative η := by
  constructor
  · rintro ⟨ζ, rfl, _⟩ x
    exact Nat.cast_nonneg _
  · intro h
    exact ⟨nnEncoding η h, nnEmbedding_nnEncoding η h,
      fun ζ hζ => nnEmbedding_injective (hζ.trans (nnEmbedding_nnEncoding η h).symm)⟩

/-- On every nonnegative bounded field, upper-only and NN stabilization coincide. -/
theorem stabilizes_nn_iff (η : Sandpile.StableField) (ξ : Counts) (w : List Site2) :
    Stabilizes (nnEmbedding η).val ξ w ↔ Sandpile.Stabilizes η ξ w := by
  exact (Sandpile.stabilizes_iff_legal_and_lt η ξ w).symm

theorem odometer_nn_eq (ξ : Counts) (η : Sandpile.StabilizationDomain ξ) :
    odometer ξ ⟨(nnEmbedding η.val).val,
      by obtain ⟨w, hw⟩ := η.property; exact ⟨w, (stabilizes_nn_iff _ _ _).mpr hw⟩⟩ =
      Sandpile.odometer ξ η := by
  obtain ⟨w, hw, he⟩ := Sandpile.odometer_spec ξ η
  exact (odometer_eq_counts ξ _ ((stabilizes_nn_iff _ _ _).mpr hw)).trans he

end
end FiniteAvalanches.Sandpile.RawFull

#print axioms FiniteAvalanches.Sandpile.RawFull.legal_prefix_le
#print axioms FiniteAvalanches.Sandpile.RawFull.existsUnique_counts
#print axioms FiniteAvalanches.Sandpile.RawFull.odometer_full_characterization
#print axioms FiniteAvalanches.Sandpile.RawFull.stabilizes_nn_iff
#print axioms FiniteAvalanches.Sandpile.RawFull.odometer_nn_eq
