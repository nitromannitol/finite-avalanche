import FiniteAvalanches.Wilson.Lattice.NestedPrefixContacts
import FiniteAvalanches.Wilson.Lattice.NestedBoxStepThree

/-! Incoming cd552a5, main.tex 513–517: the first Beurling localization bound
for actual consecutive prefixes beginning at scale 1. The one positive constant
precedes the base, obstacle, roots, source outer index, and observed stage. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.CurrentPrefixLocalization
open LatticeProb FiniteAvalanches Sandpile MeasureTheory
open Probability.CurrentScale CurrentNestedPrefix ActualLocalizationUnion
open scoped Classical ENNReal
noncomputable section

/-- Literal adjacent scales obey the source integer-power identity. -/
theorem scale_succ_eq_pow (b i : ℕ) : scale b (i + 1) = scale b i ^ b := by
  simp only [scale, pow_succ, pow_mul]

/-- Every source base and index gives a radius at least two. -/
theorem two_le_scale (b : ℕ) (hb : 6 ≤ b) (i : ℕ) : 2 ≤ scale b i := by
  have hp : 1 ≤ b ^ i := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero i (by omega : b ≠ 0))
  exact (show 2 ^ 1 ≤ 2 ^ (b ^ i) from Nat.pow_le_pow_right (by decide) hp)

/-- The source comparison i < n supplies the sixth-power outer scale internally. -/
theorem sixth_power_le_later_scale (b : ℕ) (hb : 6 ≤ b) (i n : ℕ) (hin : i < n) :
    scale b i ^ 6 ≤ scale b n := by
  calc
    scale b i ^ 6 ≤ scale b i ^ b :=
      Nat.pow_le_pow_right (scale_pos b i) hb
    _ = scale b (i + 1) := (scale_succ_eq_pow b i).symm
    _ ≤ scale b n := scale_mono b hb (by omega)

/-- Every actual requested start lies in the unpadded source query box. -/
theorem prefix_start_containment (b : ℕ) (hb : 6 ≤ b) (i : ℕ) :
    ∀ x ∈ stagePrefix b i, x ∈ boxSites (3 * scale b i + 1) :=
  prefix_subset_stage b hb i

/-- Distinct starts are exactly the complete source box at each positive stage. -/
theorem prefix_card (b : ℕ) (hb : 6 ≤ b) (i : ℕ) (hi : 1 ≤ i) :
    (stagePrefix b i).toFinset.card = (6 * scale b i + 3) ^ 2 := by
  rw [prefix_toFinset b hb i hi]
  change (boxSites (3 * scale b i + 1)).card = _
  rw [← Finset.length_toList, ReciprocalStepThree.query_list_length]

/-- The source enumeration has no repeated slots; the same bound counts actual rows. -/
theorem prefix_length (b : ℕ) (hb : 6 ≤ b) (i : ℕ) (hi : 1 ≤ i) :
    (stagePrefix b i).length = (6 * scale b i + 3) ^ 2 := by
  rw [← List.toFinset_card_of_nodup (prefix_nodup b i)]
  exact prefix_card b hb i hi

/-- Current Step 1: full terminal-inclusive stopped-prefix localization,
with all source geometric and scale hypotheses produced at the actual consumer. -/
theorem source_prefix_localization : ∃ D : ℝ, 0 < D ∧
    ∀ b : ℕ, 6 ≤ b → ∀ K : Finset (Site 2),
      ((lattice 2).induce (K : Set (Site 2))).Connected → (0 : Site 2) ∈ K →
    ∀ R : RootPair, (K : Set (Site 2)) ⊆ R.zero →
    ∀ n : ℕ, 2 ≤ n →
      16 * scale b n ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) →
    ∀ i : ℕ, 1 ≤ i → i < n →
      wilsonRows (prefixExit R (stagePrefix b i) ((scale b i) ^ 6)) ≤
        ENNReal.ofReal (D * (scale b i : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨D, hD, hbound⟩ := NestedBoxStepThree.box_list_history_escape
  refine ⟨D, hD, ?_⟩
  intro b hb K hK h0 R hKR n _hn hdiam i _hi hin
  have hmargin : 16 * scale b i ^ 6 ≤
      K.sup (fun x => K.sup (fun y => siteRadius x y)) :=
    (Nat.mul_le_mul_left 16 (sixth_power_le_later_scale b hb i n hin)).trans hdiam
  exact hbound K hK h0 R hKR (scale b i) (two_le_scale b hb i) hmargin
    (stagePrefix b i) (prefix_start_containment b hb i)

end
end FiniteAvalanches.Wilson.Lattice.CurrentPrefixLocalization
