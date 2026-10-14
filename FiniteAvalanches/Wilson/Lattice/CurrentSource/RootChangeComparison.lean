import FiniteAvalanches.Trees.RootRecoloring
import FiniteAvalanches.Wilson.Lattice.CurrentSource.RootChanges
import FiniteAvalanches.Wilson.Lattice.ColorMonotonicity

/-! Color-law comparison through cofinite intermediate roots, including the
retained roots that change color. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.CurrentRootChanges
open LatticeProb FiniteAvalanches.Trees FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Sandpile MeasureTheory Filter
open scoped Classical
noncomputable section

/-- Retained one roots in the final zero set are relabeled, preserving the total roots. -/
def reclassified (R Q : RootPair) (hone : Q.one ⊆ R.one) : RootPair where
  zero := R.zero ∪ (R.one ∩ Q.zero)
  one := Q.one
  disjoint := by
    apply Set.disjoint_left.mpr
    rintro x (hx | hx) hq
    · exact Set.disjoint_left.mp R.disjoint hx (hone hq)
    · exact Set.disjoint_left.mp Q.disjoint hx.2 hq
  zero_nonempty := R.zero_nonempty.mono Set.subset_union_left
  one_nonempty := Q.one_nonempty

theorem reclassified_total_eq (R Q : RootPair) (hone : Q.one ⊆ R.one) :
    (reclassified R Q hone).zero ∪ (reclassified R Q hone).one =
      (intermediate R Q hone).zero ∪ (intermediate R Q hone).one := by
  ext x
  constructor
  · rintro ((hx | hx) | hx)
    · exact Or.inl hx
    · exact Or.inr ⟨hx.1, Or.inl hx.2⟩
    · exact Or.inr ⟨hone hx, Or.inr hx⟩
  · rintro (hx | ⟨hr, hq | hq⟩)
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr ⟨hr, hq⟩)
    · exact Or.inr hq

theorem reclassified_zero_subset (R Q : RootPair)
    (hzero : R.zero ⊆ Q.zero) (hone : Q.one ⊆ R.one) :
    (reclassified R Q hone).zero ⊆ Q.zero := by
  rintro x (hx | hx)
  · exact hzero hx
  · exact hx.2

theorem reclassified_union_cofinite (R Q : RootPair) (hone : Q.one ⊆ R.one)
    (hR : (R.zero ∪ R.one)ᶜ.Finite) (hQ : (Q.zero ∪ Q.one)ᶜ.Finite) :
    ((reclassified R Q hone).zero ∪ (reclassified R Q hone).one)ᶜ.Finite := by
  rw [reclassified_total_eq]
  exact intermediate_union_cofinite R Q hone hR hQ

theorem wired_total_eq (R Q : RootPair)
    (htotal : R.zero ∪ R.one = Q.zero ∪ Q.one) (N : ℕ) :
    wiredZero R N ∪ wiredOne R N = wiredZero Q N ∪ wiredOne Q N := by
  ext v
  cases v with
  | none =>
    change (False ∨ True) ↔ (False ∨ True)
    rfl
  | some x =>
    change FiniteWired.site x ∈ R.zero ∪ R.one ↔
      FiniteWired.site x ∈ Q.zero ∪ Q.one
    rw [htotal]

/-- Same total roots give the same uniformly counted original-copy forests at each size. -/
theorem finite_window_root_recoloring_mono (R Q : RootPair)
    (htotal : R.zero ∪ R.one = Q.zero ∪ Q.one) (hone : Q.one ⊆ R.one)
    (N : ℕ) (W : Finset (Site 2)) (H : Set (W → Bool))
    (hH : ∀ p ∈ H, ∀ q : W → Bool,
      (∀ x, p x = true → q x = true) → q ∈ H) :
    (finiteForestLaw Q N).real (Prod.snd ⁻¹' windowColorEvent W H) ≤
      (finiteForestLaw R N).real (Prod.snd ⁻¹' windowColorEvent W H) := by
  have hoN : wiredOne Q N ⊆ wiredOne R N := by
    intro v hv
    cases v with
    | none => trivial
    | some x => exact hone hv
  rw [finite_window_real_count, finite_window_real_count]
  exact (WiredTrees.graph N).finite_root_recoloring_mono
    (wiredZero R N) (wiredOne R N) (wiredZero Q N) (wiredOne Q N)
    (wired_total_eq R Q htotal N) hoN
    (wiredWindowEvent N W H) (wiredWindowEvent_increasing N W H hH)

/-- The finite identity-forest comparison passes to the actual Wilson color laws. -/
theorem color_window_root_recoloring_mono (R Q : RootPair)
    (htotal : R.zero ∪ R.one = Q.zero ∪ Q.one) (hone : Q.one ⊆ R.one)
    (W : Finset (Site 2)) (H : Set (W → Bool))
    (hH : ∀ p ∈ H, ∀ q : W → Bool,
      (∀ x, p x = true → q x = true) → q ∈ H) :
    (wilsonColorLaw Q).real (windowColorEvent W H) ≤
      (wilsonColorLaw R).real (windowColorEvent W H) := by
  apply le_of_tendsto_of_tendsto (finite_window_real_tendsto Q W H)
    (finite_window_real_tendsto R W H)
  exact Filter.Eventually.of_forall fun N =>
    finite_window_root_recoloring_mono R Q htotal hone N W H hH

/-- One shared pair of cofinite intermediate laws realizes removal, relabeling,
and addition of precisely the current root sets. -/
theorem cofinite_root_change_comparisons (R Q : RootPair)
    (hzero : R.zero ⊆ Q.zero) (hone : Q.one ⊆ R.one)
    (hR : (R.zero ∪ R.one)ᶜ.Finite) (hQ : (Q.zero ∪ Q.one)ᶜ.Finite)
    (W : Finset (Site 2)) (H : Set (W → Bool))
    (hH : ∀ p ∈ H, ∀ q : W → Bool,
      (∀ x, p x = true → q x = true) → q ∈ H) :
    ∃ M B : RootPair,
      M = intermediate R Q hone ∧ B = reclassified R Q hone ∧
      (M.zero ∪ M.one)ᶜ.Finite ∧ (B.zero ∪ B.one)ᶜ.Finite ∧
      (wilsonColorLaw Q).real (windowColorEvent W H) ≤
        (wilsonColorLaw B).real (windowColorEvent W H) ∧
      (wilsonColorLaw B).real (windowColorEvent W H) ≤
        (wilsonColorLaw M).real (windowColorEvent W H) ∧
      (wilsonColorLaw M).real (windowColorEvent W H) ≤
        (wilsonColorLaw R).real (windowColorEvent W H) := by
  let M := intermediate R Q hone
  let B := reclassified R Q hone
  refine ⟨M, B, rfl, rfl, intermediate_union_cofinite R Q hone hR hQ,
    reclassified_union_cofinite R Q hone hR hQ, ?_, ?_, ?_⟩
  · exact color_window_zero_roots_added B Q
      (reclassified_zero_subset R Q hzero hone) rfl W H hH
  · apply color_window_root_recoloring_mono M B
      (reclassified_total_eq R Q hone).symm
    · intro x hx
      exact ⟨hone hx, Or.inr hx⟩
    · exact hH
  · exact color_window_one_roots_removed R M rfl Set.inter_subset_left W H hH

theorem color_window_mono_cofinite (R Q : RootPair)
    (hzero : R.zero ⊆ Q.zero) (hone : Q.one ⊆ R.one)
    (hR : (R.zero ∪ R.one)ᶜ.Finite) (hQ : (Q.zero ∪ Q.one)ᶜ.Finite)
    (W : Finset (Site 2)) (H : Set (W → Bool))
    (hH : ∀ p ∈ H, ∀ q : W → Bool,
      (∀ x, p x = true → q x = true) → q ∈ H) :
    (wilsonColorLaw Q).real (windowColorEvent W H) ≤
      (wilsonColorLaw R).real (windowColorEvent W H) := by
  obtain ⟨_, _, _, _, _, _, hQB, hBM, hMR⟩ :=
    cofinite_root_change_comparisons R Q hzero hone hR hQ W H hH
  exact hQB.trans (hBM.trans hMR)

end
end FiniteAvalanches.Wilson.Lattice.CurrentRootChanges
