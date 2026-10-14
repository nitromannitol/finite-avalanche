import FiniteAvalanches.Paper.Revision480.GlobalColorMonotonicity

/-! Recoloring a fixed root union changes no underlying forest; only the set of
one roots decreases. This supplies the current source's second root operation
without evaluating a non-cofinite intermediate color law. -/
set_option autoImplicit false
namespace FiniteAvalanches.Paper.Current
open LatticeProb MeasureTheory Filter FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Trees FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

theorem color_window_recolor_same_roots (R Q : RootPair)
    (hunion : R.zero ∪ R.one = Q.zero ∪ Q.one) (hone : Q.one ⊆ R.one)
    (W : Finset (Site 2)) (H : Set (W → Bool))
    (hH : ∀ p ∈ H, ∀ q : W → Bool, (∀ x, p x = true → q x = true) → q ∈ H) :
    (wilsonColorLaw Q).real (windowColorEvent W H) ≤
      (wilsonColorLaw R).real (windowColorEvent W H) := by
  apply le_of_tendsto_of_tendsto (finite_window_real_tendsto Q W H)
    (finite_window_real_tendsto R W H)
  apply Filter.Eventually.of_forall
  intro N
  have hu : (wiredRoots Q N).val = (wiredRoots R N).val := by
    ext v
    cases v with
    | none => rfl
    | some x =>
      change FiniteWired.site x ∈ Q.zero ∪ Q.one ↔ FiniteWired.site x ∈ R.zero ∪ R.one
      rw [hunion]
  have ho : wiredOne Q N ⊆ wiredOne R N := by
    intro v hv
    cases v with
    | none => trivial
    | some x => exact hone hv
  let e : FiniteForest Q N ≃ FiniteForest R N :=
    Equiv.subtypeEquivRight (fun F => by rw [hu])
  let BQ := {F : FiniteForest Q N |
    (WiredTrees.graph N).oneVertices F.val (wiredOne Q N) ∈ wiredWindowEvent N W H}
  let BR := {F : FiniteForest R N |
    (WiredTrees.graph N).oneVertices F.val (wiredOne R N) ∈ wiredWindowEvent N W H}
  have hsub (F : FiniteForest Q N) :
      (WiredTrees.graph N).oneVertices F.val (wiredOne Q N) ⊆
        (WiredTrees.graph N).oneVertices (e F).val (wiredOne R N) := by
    rintro v ⟨r, hr, hv⟩
    exact ⟨r, ho hr, hv⟩
  let f : BQ → BR := fun F => ⟨e F.val,
    wiredWindowEvent_increasing N W H hH _ F.property _ (hsub F.val)⟩
  have hf : Function.Injective f := by
    intro F F' h
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val h)
  have hc : Nat.card BQ ≤ Nat.card BR := Nat.card_le_card_of_injective f hf
  change (finiteForestLaw Q N).real (Prod.snd ⁻¹' windowColorEvent W H) ≤
    (finiteForestLaw R N).real (Prod.snd ⁻¹' windowColorEvent W H)
  rw [finite_window_real_count, finite_window_real_count, ← Nat.card_congr e]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg _)

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
theorem color_event_recolor_same_roots_cofinite (R Q : RootPair)
    (hR : (R.zero ∪ R.one)ᶜ.Finite) (hQ : (Q.zero ∪ Q.one)ᶜ.Finite)
    (hunion : R.zero ∪ R.one = Q.zero ∪ Q.one) (hone : Q.one ⊆ R.one)
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
      color_window_recolor_same_roots R Q hunion hone W H hH
    _ ≤ (wilsonColorLaw R).real E := hRle


end
end FiniteAvalanches.Paper.Current
