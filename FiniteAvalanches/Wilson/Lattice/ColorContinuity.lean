import FiniteAvalanches.Wilson.Lattice.RootContinuity

/-! Finite color laws under locally converging original root sets. Actual successful
Wilson explorations are coupled by the same increments; their measurable query
events eventually agree almost everywhere. No continuity conclusion is assumed. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice
open LatticeProb FiniteAvalanches.Trees.Lattice MeasureTheory Filter
open scoped Classical
noncomputable section

/-- Every finite JOINT query, including absent original edges, eventually agrees
under the common rows. Success AE comes from the registered fixed-root Wilson law. -/
theorem samplerEvent_eventually_iff_of_local_roots (Rj : ℕ → RootPair) (R : RootPair)
    (hl : ∀ x, ∀ᶠ j in atTop,
      (x ∈ (Rj j).zero ↔ x ∈ R.zero) ∧ (x ∈ (Rj j).one ↔ x ∈ R.one))
    (L : List (Site 2)) (B : Finset LatticeEdge) (D : Finset (Site 2))
    (pe : LatticeEdge → Bool) (pc : Site 2 → Bool) :
    ∀ᵐ ξ ∂wilsonRows, ∀ᶠ j in atTop,
      ξ ∈ samplerEvent (Rj j) L B D pe pc ↔ ξ ∈ samplerEvent R L B D pe pc := by
  filter_upwards [wilson_sampler_success_conull R L] with ξ hξ
  obtain ⟨out, hout⟩ := hξ
  obtain ⟨outj, hjout, hc, he, _⟩ := samplerRun_local_roots Rj R hl out L ξ hout
  have hfinite : ∀ᶠ j in atTop, ∀ d : D, (outj j).colors d.val = out.colors d.val :=
    eventually_all.mpr (fun d => hc d.val)
  filter_upwards [hjout, he, hfinite] with j hj hje hjc
  constructor
  · rintro ⟨st, hs, hb, hd⟩
    have hst : st = outj j := by
      rw [hj] at hs
      exact (Option.some.inj hs).symm
    subst st
    refine ⟨out, hout, ?_, ?_⟩
    · simpa only [hje] using hb
    · intro d hD
      rw [← hjc ⟨d, hD⟩]
      exact hd d hD
  · rintro ⟨st, hs, hb, hd⟩
    have hst : st = out := by
      rw [hout] at hs
      exact (Option.some.inj hs).symm
    subst st
    refine ⟨outj j, hj, ?_, ?_⟩
    · simpa only [hje] using hb
    · intro d hD
      rw [hjc ⟨d, hD⟩]
      exact hd d hD

/-- The actual finite-query probabilities converge under the SAME walk-row measure. -/
theorem samplerEvent_measure_tendsto_of_local_roots (Rj : ℕ → RootPair) (R : RootPair)
    (hl : ∀ x, ∀ᶠ j in atTop,
      (x ∈ (Rj j).zero ↔ x ∈ R.zero) ∧ (x ∈ (Rj j).one ↔ x ∈ R.one))
    (L : List (Site 2)) (B : Finset LatticeEdge) (D : Finset (Site 2))
    (pe : LatticeEdge → Bool) (pc : Site 2 → Bool) :
    Tendsto (fun j => wilsonRows (samplerEvent (Rj j) L B D pe pc)) atTop
      (nhds (wilsonRows (samplerEvent R L B D pe pc))) :=
  tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
    (measurableSet_samplerEvent R L B D pe pc)
    (fun j => measurableSet_samplerEvent (Rj j) L B D pe pc)
    (samplerEvent_eventually_iff_of_local_roots Rj R hl L B D pe pc)

/-- Every complete finite color pattern under the actual selected laws converges.
A test-pattern extension is obtained only inside this proof; no source field or
law is defined by a default outside the observed finite set. -/
theorem colorCylinder_tendsto_of_local_roots (Rj : ℕ → RootPair) (R : RootPair)
    (hl : ∀ x, ∀ᶠ j in atTop,
      (x ∈ (Rj j).zero ↔ x ∈ R.zero) ∧ (x ∈ (Rj j).one ↔ x ∈ R.one))
    (F : Finset (Site 2)) (p : F → Bool) :
    Tendsto (fun j => wilsonColorLaw (Rj j) (colorCylinder F p)) atTop
      (nhds (wilsonColorLaw R (colorCylinder F p))) := by
  obtain ⟨pc, hpc⟩ := (Subtype.val_injective : Function.Injective (Subtype.val : F → Site 2)).surjective_comp_right p
  have hpattern : colorCylinder F p = {σ : ColorField | ∀ d ∈ F, σ d = pc d} := by
    ext σ
    constructor
    · intro h d hd
      have hσ := congrFun h ⟨d, hd⟩
      have hp := congrFun hpc ⟨d, hd⟩
      exact hσ.trans hp.symm
    · intro h
      funext d
      change σ d.val = p d
      rw [h d.val d.property]
      exact congrFun hpc d
  have hprob (Q : RootPair) : wilsonColorLaw Q (colorCylinder F p) =
      wilsonRows (samplerEvent Q F.toList ∅ F (fun _ => false) pc) := by
    rw [hpattern]
    simpa only [samplerEvent, Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
      forall_const, true_and] using
      wilsonColorLaw_apply_sampler Q F.toList F pc (fun d hd => Finset.mem_toList.mpr hd)
  simp_rw [hprob]
  exact samplerEvent_measure_tendsto_of_local_roots Rj R hl F.toList ∅ F (fun _ => false) pc

/-- The full source ct:continuity conclusion with limiting nonemptiness DERIVED
from the specified common roots. This is a provider, not a new frozen anchor. -/
theorem colorCylinder_tendsto_of_fixed_roots (Rj : ℕ → RootPair)
    (A C : Set (Site 2)) (hAC : Disjoint A C) (a b : Site 2)
    (ha : ∀ j, a ∈ (Rj j).zero) (hb : ∀ j, b ∈ (Rj j).one)
    (hA : ∀ x, ∀ᶠ j in atTop, x ∈ (Rj j).zero ↔ x ∈ A)
    (hC : ∀ x, ∀ᶠ j in atTop, x ∈ (Rj j).one ↔ x ∈ C)
    (F : Finset (Site 2)) (p : F → Bool) :
    Tendsto (fun j => wilsonColorLaw (Rj j) (colorCylinder F p)) atTop
      (nhds (wilsonColorLaw (ContinuityAudit.limitRoots Rj A C hAC a b ha hb hA hC)
        (colorCylinder F p))) := by
  apply colorCylinder_tendsto_of_local_roots
  intro x
  filter_upwards [hA x, hC x] with j hjA hjC
  exact ⟨hjA, hjC⟩

end
end FiniteAvalanches.Wilson.Lattice
