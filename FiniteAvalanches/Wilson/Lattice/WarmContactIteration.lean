import FiniteAvalanches.Wilson.Lattice.WarmContactPrefixes

/-! Conditional multiplication over the actual histories after the warm-up. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.WarmContactIteration
open LatticeProb FiniteAvalanches Sandpile MeasureTheory
open BatchRestart ConditionalIteration7 ActualContactHistory ActualContactRestriction
open ActualQueryPrefixes ActualLocalizationUnion WarmContactPrefixes
open scoped Classical
noncomputable section

/-- Atom success implies iteration; consumed-row independence is proved internally. -/
theorem warm_surviving_le_pow (R : RootPair) (Q : ℕ → List (Site 2))
    (F : ℕ → Finset (Site 2)) (h : ℕ → ℕ) (t p : ℝ) (n : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hsuccess : ∀ i < n, ∀ out : SamplerState,
      (historyAtom R (warmPrefix Q i) out).Nonempty →
      (∀ path ∈ out.history, ∀ j : Fin (path.length + 1),
        path.vertex j ∈ (boxSites (h i) : Set (Site 2))) →
      p * wilsonRows.real (historyAtom R (warmPrefix Q i) out) ≤
        wilsonRows.real (historyAtom R (warmPrefix Q i) out ∩
          continuationContactEvent (initialSampler R) (warmPrefix Q (i + 1)) (F i) t)) :
    wilsonRows.real (warmSurviving R Q F h t n) ≤ (1 - p) ^ n := by
  let B := warmSurviving R Q F h t
  apply FiniteAvalanches.Probability.mass_le_pow
    (fun i => wilsonRows.real (B i)) (1 - p) (sub_nonneg.mpr hp1) measureReal_le_one n
  intro i hi
  let L := warmPrefix Q i
  let E := B i ∩ localizedPrefix R L (h i)
  let S := continuationContactEvent (initialSampler R) (L ++ Q (i + 1)) (F i) t
  have hEc : MeasurableSet[consumedRows L.length] E :=
    (measurable_warmSurviving_consumed R Q F h t i).inter
      (measurable_localizedPrefix_consumed R L (h i))
  have hE : MeasurableSet E := consumedRows_le L.length E hEc
  have hS : MeasurableSet S := measurable_continuationContactEvent _ _ _ _
  let outputs := {out : SamplerState | (historyAtom R L out).Nonempty}
  have hc : outputs.Countable := reachable_states_countable R L
  letI := hc.toEncodable
  let A (out : outputs) := E ∩ historyAtom R L out.val
  have hA (out : outputs) : MeasurableSet (A out) :=
    hE.inter (fullHistory_le R L _ (measurable_historyAtom R L out.val))
  have hdis : Pairwise (fun a b : outputs => Disjoint (A a) (A b)) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    intro ξ ha hb
    apply hab
    apply Subtype.ext
    exact Option.some.inj (ha.2.symm.trans hb.2)
  have hunion : (⋃ out : outputs, A out) = E := by
    ext ξ
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨out, hξ⟩
      exact hξ.1
    · intro hξ
      obtain ⟨out, hs, _⟩ := hξ.2
      exact ⟨⟨out, ⟨ξ, hs⟩⟩, hξ, hs⟩
  have hmass (out : outputs) : p * wilsonRows.real (A out) ≤ wilsonRows.real (A out ∩ S) := by
    by_cases hex : (A out).Nonempty
    · obtain ⟨ξ, hξ⟩ := hex
      have hs : samplerRun (initialSampler R) L ξ = some out.val := hξ.2
      obtain ⟨out', hs', hstay⟩ := hξ.1.2
      have he : out' = out.val := Option.some.inj (hs'.symm.trans hs)
      subst out'
      have hb := hsuccess i hi out.val out.property hstay
      change p * wilsonRows.real (historyAtom R L out.val) ≤
        wilsonRows.real (historyAtom R L out.val ∩ S) at hb
      exact restricted_atom_success R L (Q (i + 1)) out.val E hEc (F i) t p hb
    · rw [Set.not_nonempty_iff_eq_empty.mp hex, Set.empty_inter, measureReal_empty, mul_zero]
  have hmassENN (out : outputs) :
      ENNReal.ofReal p * wilsonRows (A out) ≤ wilsonRows (A out ∩ S) := by
    have hm := ENNReal.ofReal_le_ofReal (hmass out)
    rw [ENNReal.ofReal_mul hp0] at hm
    simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hm
  have hsuccessENN : ENNReal.ofReal p * wilsonRows E ≤ wilsonRows (E ∩ S) := by
    have hdS : Pairwise (fun a b : outputs => Disjoint (A a ∩ S) (A b ∩ S)) :=
      fun _ _ hab => (hdis hab).mono Set.inter_subset_left Set.inter_subset_left
    calc
      _ = ENNReal.ofReal p * ∑' out : outputs, wilsonRows (A out) := by
        rw [← hunion, measure_iUnion hdis hA]
      _ = ∑' out : outputs, ENNReal.ofReal p * wilsonRows (A out) := ENNReal.tsum_mul_left.symm
      _ ≤ ∑' out : outputs, wilsonRows (A out ∩ S) := ENNReal.tsum_le_tsum hmassENN
      _ = wilsonRows (E ∩ S) := by
        rw [← measure_iUnion hdS (fun out => (hA out).inter hS), ← Set.iUnion_inter, hunion]
  have hsucc : p * wilsonRows.real E ≤ wilsonRows.real (E ∩ S) := by
    have hm := ENNReal.toReal_mono (measure_ne_top _ _) hsuccessENN
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp0, Measure.real] using hm
  have hsplit := measureReal_inter_add_sdiff (μ := wilsonRows) (s := E) hS
  have hnext : B (i + 1) = E \ S := rfl
  rw [hnext]
  calc
    wilsonRows.real (E \ S) ≤ (1 - p) * wilsonRows.real E := by
      nlinarith only [hsplit, hsucc]
    _ ≤ (1 - p) * wilsonRows.real (B i) :=
      mul_le_mul_of_nonneg_left (measureReal_mono Set.inter_subset_left) (sub_nonneg.mpr hp1)

end
end FiniteAvalanches.Wilson.Lattice.WarmContactIteration
