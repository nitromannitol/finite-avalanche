import FiniteAvalanches.Paper.Current.Recoloring
import FiniteAvalanches.Wilson.Lattice.UnorderedContacts

/-! Current cd552a fo:lattice-monotonicity, using the source's retained-one-root
intermediate pair and the unordered extended contact statistic for every V. -/
set_option autoImplicit false
namespace FiniteAvalanches.Paper.Current
open LatticeProb MeasureTheory FiniteAvalanches.Wilson.Lattice
open scoped Classical ENNReal
noncomputable section

/-- Exact four-set color conclusion, with the current source's two-step intermediate roots. -/
theorem source_four_sets_global_mono
    (A A' Γ Γ' : Set (Site 2)) (hA : A.Nonempty) (hΓ' : Γ'.Nonempty)
    (hzero : A ⊆ A') (hone : Γ' ⊆ Γ)
    (hdR : Disjoint A Γ) (hdQ : Disjoint A' Γ')
    (hR : (A ∪ Γ)ᶜ.Finite) (hQ : (A' ∪ Γ')ᶜ.Finite)
    (E : Set ColorField) (hE : MeasurableSet E)
    (hup : ∀ p ∈ E, ∀ q : ColorField,
      (∀ x, p x = true → q x = true) → q ∈ E) :
    let R : RootPair := ⟨A, Γ, hdR, hA, hΓ'.mono hone⟩
    let Q : RootPair := ⟨A', Γ', hdQ, hA.mono hzero, hΓ'⟩
    (wilsonColorLaw Q).real E ≤ (wilsonColorLaw R).real E := by
  let R : RootPair := ⟨A, Γ, hdR, hA, hΓ'.mono hone⟩
  let Q : RootPair := ⟨A', Γ', hdQ, hA.mono hzero, hΓ'⟩
  let C := Γ ∩ (A' ∪ Γ')
  have hC : Γ' ⊆ C := fun x hx => ⟨hone hx, Or.inr hx⟩
  let M : RootPair := ⟨A, C, hdR.mono_right (fun _ h => h.1), hA, hΓ'.mono hC⟩
  have hM : (M.zero ∪ M.one)ᶜ.Finite := by
    apply (hR.union hQ).subset
    intro x hx
    by_cases hxr : x ∈ A ∪ Γ
    · right
      intro hxq
      apply hx
      rcases hxr with hxa | hxg
      · exact Or.inl hxa
      · exact Or.inr ⟨hxg, hxq⟩
    · exact Or.inl hxr
  have hfirst : (wilsonColorLaw M).real E ≤ (wilsonColorLaw R).real E :=
    FiniteAvalanches.Paper.Revision480.color_event_mono_cofinite R M hR hM
      (Set.Subset.refl A) (fun _ h => h.1) E hE hup
  have hAB : A ⊆ A' \ C := by
    intro x hx
    exact ⟨hzero hx, fun hc => Set.disjoint_left.mp hdR hx hc.1⟩
  let B : RootPair := ⟨A' \ C, C, Set.disjoint_sdiff_left, hA.mono hAB, hΓ'.mono hC⟩
  have hB : (B.zero ∪ B.one)ᶜ.Finite := by
    apply hM.subset
    intro x hx hm
    apply hx
    rcases hm with ha | hc
    · exact Or.inl (hAB ha)
    · exact Or.inr hc
  have hBQ : B.zero ∪ B.one = Q.zero ∪ Q.one := by
    ext x
    constructor
    · rintro (ha | hc)
      · exact Or.inl ha.1
      · exact hc.2
    · rintro (ha | hc)
      · by_cases hx : x ∈ C
        · exact Or.inr hx
        · exact Or.inl ⟨ha, hx⟩
      · exact Or.inr (hC hc)
  have hadd : (wilsonColorLaw B).real E ≤ (wilsonColorLaw M).real E :=
    FiniteAvalanches.Paper.Revision480.color_event_mono_cofinite M B hM hB hAB
      (Set.Subset.refl C) E hE hup
  have hrecolor : (wilsonColorLaw Q).real E ≤ (wilsonColorLaw B).real E :=
    color_event_recolor_same_roots_cofinite B Q hB hQ hBQ hC E hE hup
  exact (hrecolor.trans hadd).trans hfirst

/-- The current arbitrary-set contact law is stochastically dominated, including infinity. -/
theorem source_unordered_contact_event_mono
    (A A' Γ Γ' : Set (Site 2)) (hA : A.Nonempty) (hΓ' : Γ'.Nonempty)
    (hzero : A ⊆ A') (hone : Γ' ⊆ Γ)
    (hdR : Disjoint A Γ) (hdQ : Disjoint A' Γ')
    (hR : (A ∪ Γ)ᶜ.Finite) (hQ : (A' ∪ Γ')ᶜ.Finite)
    (V : Set (Site 2)) (D : Set ℝ≥0∞) (hD : MeasurableSet D)
    (hup : ∀ n ∈ D, ∀ m : ℝ≥0∞, n ≤ m → m ∈ D) :
    let R : RootPair := ⟨A, Γ, hdR, hA, hΓ'.mono hone⟩
    let Q : RootPair := ⟨A', Γ', hdQ, hA.mono hzero, hΓ'⟩
    (wilsonColorLaw Q).real {σ | unorderedContacts V σ ∈ D} ≤
      (wilsonColorLaw R).real {σ | unorderedContacts V σ ∈ D} := by
  exact source_four_sets_global_mono A A' Γ Γ' hA hΓ' hzero hone hdR hdQ hR hQ
    (unorderedContacts V ⁻¹' D) ((measurable_unorderedContacts V) hD)
    (fun p hp q hpq => hup _ hp _ (unorderedContacts_mono V hpq))

/-- Tail comparisons use the extended count without discarding infinite contacts. -/
theorem source_unordered_contact_tail_mono
    (A A' Γ Γ' : Set (Site 2)) (hA : A.Nonempty) (hΓ' : Γ'.Nonempty)
    (hzero : A ⊆ A') (hone : Γ' ⊆ Γ)
    (hdR : Disjoint A Γ) (hdQ : Disjoint A' Γ')
    (hR : (A ∪ Γ)ᶜ.Finite) (hQ : (A' ∪ Γ')ᶜ.Finite)
    (V : Set (Site 2)) (t : ℝ≥0∞) :
    let R : RootPair := ⟨A, Γ, hdR, hA, hΓ'.mono hone⟩
    let Q : RootPair := ⟨A', Γ', hdQ, hA.mono hzero, hΓ'⟩
    (wilsonColorLaw Q).real {σ | t ≤ unorderedContacts V σ} ≤
      (wilsonColorLaw R).real {σ | t ≤ unorderedContacts V σ} := by
  exact source_unordered_contact_event_mono A A' Γ Γ' hA hΓ' hzero hone hdR hdQ hR hQ
    V (Set.Ici t) measurableSet_Ici (fun _ hn _ hnm => hn.trans hnm)

end
end FiniteAvalanches.Paper.Current
