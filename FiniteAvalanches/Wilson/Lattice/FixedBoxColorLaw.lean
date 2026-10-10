import FiniteAvalanches.Wilson.Lattice.FiniteBoxColors
import FiniteAvalanches.Wilson.Lattice.ColorMonotonicity

/-! A finite box containing every non-one site already has the exact lattice
Wilson color-cylinder law. The finite copied-forest equivalence is proved
internally; only the existing registered colored-Wilson weak limit is used. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.WiredBoxCopies
open LatticeProb FiniteAvalanches.Sandpile MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section

/-- The complete uniform copied-forest denominator is retained on both boxes. -/
theorem finite_window_real_eq {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one)
    (W : Finset (Site 2)) (H : Set (W → Bool)) :
    (finiteForestLaw R N).real (Prod.snd ⁻¹' windowColorEvent W H) =
      (finiteForestLaw R M).real (Prod.snd ⁻¹' windowColorEvent W H) := by
  have hm : MeasurableSet (Prod.snd ⁻¹' windowColorEvent W H : Set ForestField) :=
    ((isClopen_windowColorEvent W H).preimage continuous_snd).isClosed.measurableSet
  have hevent (F : FiniteForest R N) :
      finiteForestField R N F ∈ Prod.snd ⁻¹' windowColorEvent W H ↔
        finiteForestField R M (finiteForestEquiv hNM R houtside F) ∈
          Prod.snd ⁻¹' windowColorEvent W H := by
    change (fun x : W => finiteColors R N F (wiredSite N x.val)) ∈ H ↔
      (fun x : W => finiteColors R M (finiteForestEquiv hNM R houtside F)
        (wiredSite M x.val)) ∈ H
    have hc : (fun x : W => finiteColors R N F (wiredSite N x.val)) =
        (fun x : W => finiteColors R M (finiteForestEquiv hNM R houtside F)
          (wiredSite M x.val)) := by
      funext x
      exact (finiteForestEquiv_site_colors hNM R houtside F x.val).symm
    rw [hc]
  have hcount := Nat.card_congr ((finiteForestEquiv hNM R houtside).subtypeEquiv
    (p := fun F => finiteForestField R N F ∈ Prod.snd ⁻¹' windowColorEvent W H)
    (q := fun F => finiteForestField R M F ∈ Prod.snd ⁻¹' windowColorEvent W H) hevent)
  rw [Measure.real,Measure.real,finiteForestLaw_count R N _ hm,
    finiteForestLaw_count R M _ hm]
  simp only [ENNReal.toReal_div,ENNReal.toReal_natCast]
  change (Nat.card {F : FiniteForest R N //
      finiteForestField R N F ∈ Prod.snd ⁻¹' windowColorEvent W H} : ℝ) /
      finiteForestCount R N =
    (Nat.card {F : FiniteForest R M //
      finiteForestField R M F ∈ Prod.snd ⁻¹' windowColorEvent W H} : ℝ) /
      finiteForestCount R M
  rw [hcount,finiteForestCount_eq hNM R houtside]

/-- Exact fixed-box identification on every finite window and every event,
without a Wilson restart or color-law equality supplied as a hypothesis. -/
theorem fixed_box_window_real (R : RootPair) (N : ℕ)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one)
    (W : Finset (Site 2)) (H : Set (W → Bool)) :
    (finiteForestLaw R N).real (Prod.snd ⁻¹' windowColorEvent W H) =
      (wilsonColorLaw R).real (windowColorEvent W H) := by
  have hconst : Tendsto
      (fun M => (finiteForestLaw R M).real (Prod.snd ⁻¹' windowColorEvent W H))
      atTop (nhds ((finiteForestLaw R N).real (Prod.snd ⁻¹' windowColorEvent W H))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with M hM
    exact finite_window_real_eq hM R houtside W H
  exact tendsto_nhds_unique hconst (finite_window_real_tendsto R W H)

/-- Source-ready actual whole-forest count ratio, for arbitrary finite color
observations. This does not assert the observed-tree conditional identity. -/
theorem fixed_box_window_real_count (R : RootPair) (N : ℕ)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one)
    (W : Finset (Site 2)) (H : Set (W → Bool)) :
    (wilsonColorLaw R).real (windowColorEvent W H) =
      (Nat.card {F : FiniteForest R N |
        finiteForestField R N F ∈ Prod.snd ⁻¹' windowColorEvent W H} : ℝ) /
        finiteForestCount R N := by
  rw [← fixed_box_window_real R N houtside W H,Measure.real,
    finiteForestLaw_count R N _
      (((isClopen_windowColorEvent W H).preimage continuous_snd).isClosed.measurableSet)]
  simp only [ENNReal.toReal_div,ENNReal.toReal_natCast]

end
end FiniteAvalanches.Wilson.Lattice.WiredBoxCopies
