import FiniteAvalanches.Wilson.Lattice.CurrentSource.RootChangeComparison
import Mathlib.MeasureTheory.Measure.Real

/-! Global color comparison when both entire root unions have finite complement. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.CurrentRootChanges
open LatticeProb MeasureTheory FiniteAvalanches.Wilson.Lattice
open scoped Classical
noncomputable section

private def completeOneBackground (Q : RootPair) (W : Finset (Site 2))
    (p : W → Bool) : ColorField :=
  fun x => if hx : x ∈ W then p ⟨x, hx⟩ else decide (x ∈ Q.one)

private theorem completeOneBackground_mono (Q : RootPair) (W : Finset (Site 2))
    (p q : W → Bool) (hpq : ∀ x, p x = true → q x = true) :
    ∀ x, completeOneBackground Q W p x = true →
      completeOneBackground Q W q x = true := by
  intro x hx
  by_cases hxW : x ∈ W
  · simpa only [completeOneBackground, dif_pos hxW] using
      hpq ⟨x, hxW⟩ (by simpa only [completeOneBackground, dif_pos hxW] using hx)
  · simpa only [completeOneBackground, dif_neg hxW] using hx

private theorem color_real_eq_joint_real (R : RootPair)
    (E : Set ColorField) (hE : MeasurableSet E) :
    (wilsonColorLaw R).real E =
      (wilsonLaw R : Measure ForestField).real (Prod.snd ⁻¹' E) := by
  exact map_measureReal_apply measurable_snd hE

/-- Global stochastic order for the actual Wilson color laws with cofinite root unions. -/
theorem color_event_mono_cofinite (R Q : RootPair)
    (hR : (R.zero ∪ R.one)ᶜ.Finite) (hQ : (Q.zero ∪ Q.one)ᶜ.Finite)
    (hzero : R.zero ⊆ Q.zero) (hone : Q.one ⊆ R.one)
    (E : Set ColorField) (hE : MeasurableSet E)
    (hup : ∀ p ∈ E, ∀ q : ColorField,
      (∀ x, p x = true → q x = true) → q ∈ E) :
    (wilsonColorLaw Q).real E ≤ (wilsonColorLaw R).real E := by
  let W : Finset (Site 2) := hR.toFinset ∪ hQ.toFinset
  let H : Set (W → Bool) := {p | completeOneBackground Q W p ∈ E}
  have hH : ∀ p ∈ H, ∀ q : W → Bool,
      (∀ x, p x = true → q x = true) → q ∈ H := by
    intro p hp q hpq
    exact hup _ hp _ (completeOneBackground_mono Q W p q hpq)
  have hwindow : MeasurableSet (windowColorEvent W H) :=
    (isClopen_windowColorEvent W H).isClosed.measurableSet
  have hQoutside : ∀ x, x ∉ W → x ∈ Q.zero ∪ Q.one := by
    intro x hxW
    by_contra hx
    apply hxW
    exact Finset.mem_union.mpr (Or.inr (hQ.mem_toFinset.mpr hx))
  have hQeq : (wilsonColorLaw Q).real E =
      (wilsonColorLaw Q).real (windowColorEvent W H) := by
    rw [color_real_eq_joint_real Q E hE,
      color_real_eq_joint_real Q (windowColorEvent W H) hwindow]
    apply measureReal_congr
    filter_upwards [wilsonLaw_ae_root_colors Q] with ω hω
    have heq : completeOneBackground Q W (fun x : W => ω.2 x.val) = ω.2 := by
      funext x
      by_cases hxW : x ∈ W
      · simp only [completeOneBackground, dif_pos hxW]
      · by_cases hxone : x ∈ Q.one
        · simp only [completeOneBackground, dif_neg hxW,
            decide_eq_true hxone, hω.1 x hxone]
        · have hxzero : x ∈ Q.zero := (hQoutside x hxW).resolve_right hxone
          simp only [completeOneBackground, dif_neg hxW,
            decide_eq_false hxone, hω.2 x hxzero]
    apply propext
    change ω.2 ∈ E ↔ completeOneBackground Q W (fun x : W => ω.2 x.val) ∈ E
    rw [heq]
  have hRsub : (Prod.snd ⁻¹' windowColorEvent W H : Set ForestField)
      ≤ᵐ[(wilsonLaw R : Measure ForestField)] Prod.snd ⁻¹' E := by
    filter_upwards [wilsonLaw_ae_root_colors R] with ω hω
    intro hωH
    change completeOneBackground Q W (fun x : W => ω.2 x.val) ∈ E at hωH
    apply hup _ hωH ω.2
    intro x hxtrue
    by_cases hxW : x ∈ W
    · simpa only [completeOneBackground, dif_pos hxW] using hxtrue
    · have hxone : x ∈ Q.one := of_decide_eq_true
        (by simpa only [completeOneBackground, dif_neg hxW] using hxtrue)
      exact hω.1 x (hone hxone)
  have hRle : (wilsonColorLaw R).real (windowColorEvent W H) ≤
      (wilsonColorLaw R).real E := by
    rw [color_real_eq_joint_real R (windowColorEvent W H) hwindow,
      color_real_eq_joint_real R E hE]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hRsub)
  calc
    (wilsonColorLaw Q).real E =
        (wilsonColorLaw Q).real (windowColorEvent W H) := hQeq
    _ ≤ (wilsonColorLaw R).real (windowColorEvent W H) :=
      color_window_mono_cofinite R Q hzero hone hR hQ W H hH
    _ ≤ (wilsonColorLaw R).real E := hRle

end
end FiniteAvalanches.Wilson.Lattice.CurrentRootChanges
