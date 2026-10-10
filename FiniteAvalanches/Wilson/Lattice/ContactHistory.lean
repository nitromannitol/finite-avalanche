import FiniteAvalanches.Wilson.Lattice.RevealedRestart
import FiniteAvalanches.Wilson.Lattice.ConditionalHistory

/-! Contact success on an actual full-history atom, partitioned by every finite
neighbor-color pattern of the literal contact event. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.ActualContactHistory
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory
open BatchRestart ConditionalIteration7 ActualRevealedRestart
open scoped Classical
noncomputable section

/-- A successful finite query observes the actual contact event through all its
neighbor colors. No value is assigned to an unknown sampler color. -/
def continuationContactEvent (st : SamplerState) (Q : List (Site 2))
    (F : Finset (Site 2)) (t : ℝ) : Set Rows :=
  {ξ | ∃ next, samplerRun st Q ξ = some next ∧
    ∃ σ ∈ contactEvent F t, ∀ d ∈ contactSites F, next.colors d = some (σ d)}

/-- Finite contact-pattern masses transfer to the actual continuation on the
whole history atom, using the independent rows after the prefix. -/
theorem history_contact_success_mass (R : RootPair) (L Q : List (Site 2))
    (ξ₀ : Rows) (out : SamplerState) (hs : samplerRun (initialSampler R) L ξ₀ = some out)
    (F : Finset (Site 2)) (t : ℝ) (hQ : ∀ d ∈ contactSites F, d ∈ Q) :
    (wilsonColorLaw (restartedRoots R L ξ₀ out hs)).real (contactEvent F t) *
        wilsonRows.real (historyAtom R L out) ≤
      wilsonRows.real (historyAtom R L out ∩
        continuationContactEvent (initialSampler R) (L ++ Q) F t) := by
  let D := contactSites F
  let P := {p : D → Bool // ∃ σ ∈ contactEvent F t, ∀ d : D, σ d.val = p d}
  letI : Fintype P := Fintype.ofFinite P
  let representative (p : P) : ColorField := Classical.choose p.property
  have hrep (p : P) : representative p ∈ contactEvent F t ∧
      ∀ d : D, representative p d.val = p.val d := Classical.choose_spec p.property
  let B (p : P) : Set ColorField := {σ | ∀ d ∈ D, σ d = representative p d}
  let A (p : P) := continuationPattern (initialSampler R) (L ++ Q) D (representative p)
  let H := historyAtom R L out
  have hBunion : (⋃ p : P, B p) = contactEvent F t := by
    ext σ
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨p, hp⟩
      have he := contacts_of_agree F (fun d hd => hp d hd)
      change t ≤ (contacts F σ : ℝ)
      rw [he]
      exact (hrep p).1
    · intro hσ
      let p : P := ⟨fun d => σ d.val, σ, hσ, fun _ => rfl⟩
      refine ⟨p, fun d hd => ?_⟩
      exact ((hrep p).2 ⟨d, hd⟩).symm
  have hAunion : (⋃ p : P, A p) =
      continuationContactEvent (initialSampler R) (L ++ Q) F t := by
    ext ξ
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨p, next, hn, hp⟩
      exact ⟨next, hn, representative p, (hrep p).1, hp⟩
    · rintro ⟨next, hn, σ, hσ, hp⟩
      let p : P := ⟨fun d => σ d.val, σ, hσ, fun _ => rfl⟩
      refine ⟨p, next, hn, fun d hd => ?_⟩
      rw [hp d hd]
      exact congrArg some ((hrep p).2 ⟨d, hd⟩).symm
  have hBdisjoint : Pairwise (fun p q => Disjoint (B p) (B q)) := by
    intro p q hpq
    apply Set.disjoint_left.mpr
    intro σ hp hq
    apply hpq
    apply Subtype.ext
    funext d
    calc
      p.val d = representative p d.val := ((hrep p).2 d).symm
      _ = σ d.val := (hp d.val d.property).symm
      _ = representative q d.val := hq d.val d.property
      _ = q.val d := (hrep q).2 d
  have hAdisjoint : Pairwise (fun p q => Disjoint (A p) (A q)) := by
    intro p q hpq
    apply Set.disjoint_left.mpr
    rintro ξ ⟨next, hn, hp⟩ ⟨next', hn', hq⟩
    have he : next = next' := Option.some.inj (hn.symm.trans hn')
    subst next'
    apply hpq
    apply Subtype.ext
    funext d
    calc
      p.val d = representative p d.val := ((hrep p).2 d).symm
      _ = representative q d.val := Option.some.inj
        ((hp d.val d.property).symm.trans (hq d.val d.property))
      _ = q.val d := (hrep q).2 d
  have hBm (p : P) : MeasurableSet (B p) := by
    have he : B p = ⋂ d ∈ D, {σ : ColorField | σ d = representative p d} := by
      ext σ
      simp only [B, Set.mem_setOf_eq, Set.mem_iInter]
    rw [he]
    exact Finset.measurableSet_biInter D (fun d _ =>
      (isClosed_eq (continuous_apply d : Continuous (fun σ : ColorField => σ d))
        continuous_const).measurableSet)
  have hAm (p : P) : MeasurableSet (A p) := measurable_continuationPattern _ _ _ _
  have hH : MeasurableSet H := fullHistory_le R L H (measurable_historyAtom R L out)
  have hmass (p : P) :
      (wilsonColorLaw (restartedRoots R L ξ₀ out hs)).real (B p) * wilsonRows.real H ≤
        wilsonRows.real (H ∩ A p) := by
    have hi := history_success_mass_of_root_law_lower_bound R L Q ξ₀ out hs D
      (representative p) hQ
      ((wilsonColorLaw (restartedRoots R L ξ₀ out hs)).real (B p)) le_rfl
    rw [setIntegral_indicator (hAm p), setIntegral_const, smul_eq_mul, mul_one] at hi
    exact hi
  have hIdisjoint : Pairwise (fun p q => Disjoint (H ∩ A p) (H ∩ A q)) := by
    intro p q hpq
    exact (hAdisjoint hpq).mono Set.inter_subset_right Set.inter_subset_right
  calc
    _ = (∑ p : P, (wilsonColorLaw (restartedRoots R L ξ₀ out hs)).real (B p)) *
        wilsonRows.real H := by
      rw [← hBunion, measureReal_iUnion_fintype hBdisjoint hBm]
    _ = ∑ p : P, (wilsonColorLaw (restartedRoots R L ξ₀ out hs)).real (B p) *
        wilsonRows.real H := Finset.sum_mul _ _ _
    _ ≤ ∑ p : P, wilsonRows.real (H ∩ A p) := Finset.sum_le_sum (fun p _ => hmass p)
    _ = wilsonRows.real (H ∩ continuationContactEvent (initialSampler R) (L ++ Q) F t) := by
      rw [← measureReal_iUnion_fintype hIdisjoint (fun p => hH.inter (hAm p)),
        ← Set.inter_iUnion, hAunion]

/-- A universal revealed-root estimate yields actual conditional intersection
mass for every successful confined history and every covering continuation. -/
theorem internal_history_contact_mass_of_revealed_estimate (ε : ℝ)
    (hrevealed : ∃ κ : ℕ, 30 ≤ κ ∧
      ∀ (K : Finset (Site 2)) (γ : SimpleRay),
        ((lattice 2).induce (K : Set (Site 2))).Connected →
        0 ∈ K → Disjoint (K : Set (Site 2)) γ.vertices →
        (lattice 2).Adj 0 (γ.vertex 0) →
        ∀ (h r : ℕ), 10 ≤ h → h ^ κ ≤ r →
        16 * r ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) →
        ∀ (R : RootPair), (K : Set (Site 2)) ⊆ R.zero →
          R.zero ⊆ (K : Set (Site 2)) ∪ (boxSites h : Set (Site 2)) →
          γ.vertices ⊆ R.one →
          ε / 2 ≤ (wilsonColorLaw R).real
            (kContactEvent K (3 * (r : ℝ)) ((1 / 16 : ℝ) * Real.log (r : ℝ)))) :
    ∃ κ : ℕ, 30 ≤ κ ∧
      ∀ (K : Finset (Site 2)) (γ : SimpleRay)
        (hK : ((lattice 2).induce (K : Set (Site 2))).Connected) (h0 : 0 ∈ K)
        (hd : Disjoint (K : Set (Site 2)) γ.vertices)
        (ha : (lattice 2).Adj 0 (γ.vertex 0))
        (h r : ℕ), 10 ≤ h → h ^ κ ≤ r →
        16 * r ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) →
        ∀ (L : List (Site 2)) (ξ : ℕ → WalkDriver) (out : SamplerState)
          (_hs : samplerRun (initialSampler
            (prependConnectingPair K hK γ 0 h0 ha
              (fun n hn => Set.disjoint_left.mp hd hn ⟨n, rfl⟩)).roots) L ξ = some out),
          (∀ p ∈ out.history, ∀ j : Fin (p.length + 1),
            p.vertex j ∈ (boxSites h : Set (Site 2))) →
          ∀ Q : List (Site 2),
            (∀ d ∈ contactSites (K.filter
              (fun x => (siteRadius 0 x : ℝ) ≤ 3 * (r : ℝ))), d ∈ Q) →
            let R := (prependConnectingPair K hK γ 0 h0 ha
              (fun n hn => Set.disjoint_left.mp hd hn ⟨n, rfl⟩)).roots
            (ε / 2) * wilsonRows.real (historyAtom R L out) ≤
              wilsonRows.real (historyAtom R L out ∩
                continuationContactEvent (initialSampler R) (L ++ Q)
                  (K.filter (fun x => (siteRadius 0 x : ℝ) ≤ 3 * (r : ℝ)))
                  ((1 / 16 : ℝ) * Real.log (r : ℝ))) := by
  obtain ⟨κ, hκ, hbound⟩ := internal_restarted_contact_bound_of_revealed_estimate ε hrevealed
  refine ⟨κ, hκ, ?_⟩
  intro K γ hK h0 hd ha h r hh hr hdiam L ξ out hs hstay Q hQ
  have hb := hbound K γ hK h0 hd ha h r hh hr hdiam L ξ out hs hstay
  calc
    _ ≤ (wilsonColorLaw (restartedRoots _ L ξ out hs)).real
          (kContactEvent K (3 * (r : ℝ)) ((1 / 16 : ℝ) * Real.log (r : ℝ))) *
        wilsonRows.real (historyAtom _ L out) :=
      mul_le_mul_of_nonneg_right hb measureReal_nonneg
    _ ≤ _ := history_contact_success_mass _ L Q ξ out hs _ _ hQ

end
end FiniteAvalanches.Wilson.Lattice.ActualContactHistory
