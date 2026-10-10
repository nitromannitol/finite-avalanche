import FiniteAvalanches.Wilson.Lattice.JointWitnessBounds
import FiniteAvalanches.Wilson.Lattice.CofiniteReciprocalGeometry
import FiniteAvalanches.Probability.Multiscale.StepSixIncoming

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.CofiniteReciprocalAssembly
open LatticeProb FiniteAvalanches Sandpile MeasureTheory
open CofiniteClosedContactConsumer JointWitnessBounds CofiniteReciprocalGeometry Translation
open FiniteAvalanches.Probability.Multiscale.StepSixIncoming
open scoped Classical
noncomputable section

/-- One positive exponent and constant precede every origin source geometry. -/
theorem origin_reciprocal_of_open_joint_v3
    (hjoint : (∃ ε : ℝ, 0 < ε ∧
  (∀ (r : ℕ), 10 ^ 30 ≤ r → ∀ (R : RootPair),
    (R.zero ∪ R.one)ᶜ.Finite →
    0 ∈ R.zero →
    (∃ b ∈ R.one, (lattice 2).Adj 0 b) →
    ((lattice 2).induce R.zero).Connected →
    (∃ x ∈ R.zero, 2 * r ≤ siteRadius 0 x) →
    ((lattice 2).induce R.one).Connected →
    (∃ y ∈ R.one, siteRadius 0 y = r) →
    ε ≤ (wilsonColorLaw R).real
      (localContactEvent R.zero 0 (2 * r) ((1 / 8 : ℝ) * Real.log (r : ℝ)))) ∧
  (∃ κ : ℕ, 30 ≤ κ ∧
    ∀ (K : Finset (Site 2)) (γ : Set (Site 2)),
      ((lattice 2).induce (K : Set (Site 2))).Connected →
      0 ∈ K → Disjoint (K : Set (Site 2)) γ →
      ((lattice 2).induce γ).Connected → γᶜ.Finite →
      (∃ b ∈ γ, (lattice 2).Adj 0 b) →
      ∀ (h r : ℕ), 10 ≤ h → h ^ κ ≤ r →
      16 * r ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) →
      ∀ (R : RootPair), (K : Set (Site 2)) ⊆ R.zero →
        R.zero ⊆ (K : Set (Site 2)) ∪ (boxSites h : Set (Site 2)) →
        γ ⊆ R.one →
        ε / 2 ≤ (wilsonColorLaw R).real
          (kContactEvent K (3 * (r : ℝ)) ((1 / 16 : ℝ) * Real.log (r : ℝ)))))) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ K : Finset (Site 2),
    ((lattice 2).induce (K : Set (Site 2))).Connected →
    ∀ γ : Set (Site 2), ((lattice 2).induce γ).Connected →
      γᶜ.Finite → Disjoint (K : Set (Site 2)) γ →
      (0 : Site 2) ∈ K → (∃ b ∈ γ, (lattice 2).Adj 0 b) →
      ∀ R : RootPair, R.zero = (K : Set (Site 2)) → R.one = γ →
        (∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw R) ≤
          C * Real.rpow
            (Real.log (((K.sup (fun x => K.sup (fun y => siteRadius x y)) : ℕ) : ℝ) + 2))
            (-a) := by
  obtain ⟨ε, hε, hlocal, κ, hκ, D, _hD, hlow⟩ :=
    actual_source_global_closed_tail_of_open_joint_v3 hjoint
  have hε' : ε ≤ 1 := epsilon_le_one_of_local ε hlocal
  obtain ⟨a, C, ha, hC, hscalar⟩ :=
    exists_reciprocal_log_bound_of_small_counts.{0} ε κ D hε hε' hκ
  refine ⟨a, C, ha, hC, ?_⟩
  intro K hK γ hconn hfinite hd h0 hb R hzero hone
  have hpos := actual_contacts_pos K γ h0 hb R hone
  have hmeas := (actual_contacts_finite_measurable K).2
  have hbad : ∀ n : ℕ, 1 ≤ n →
      16 * ((2 : ℝ) ^ ((6 * κ) ^ (2 * n - 1))) ≤
        ((K.sup (fun x => K.sup (fun y => siteRadius x y)) : ℕ) : ℝ) →
      (wilsonColorLaw R).real
        {σ : ColorField | (contacts K σ : ℝ) <
          (1 / 16 : ℝ) * Real.log ((2 : ℝ) ^ ((6 * κ) ^ n))} ≤
        (1 - ε / 2) ^ n +
          2 * D * ((2 : ℝ) ^ ((6 * κ) ^ (n - 1))) ^ (-(1 / 2 : ℝ)) := by
    intro n hn hdiam
    have hclosed := hlow K γ hK h0 hd hconn hfinite hb R hzero hone n hn hdiam
    have hsub : {σ : ColorField | (contacts K σ : ℝ) <
        (1 / 16 : ℝ) * Real.log ((2 : ℝ) ^ ((6 * κ) ^ n))} ⊆
        {σ : ColorField | (contacts K σ : ℝ) ≤
          (1 / 16 : ℝ) * Real.log ((2 : ℝ) ^ ((6 * κ) ^ n))} :=
      by
        intro σ hσ
        change (contacts K σ : ℝ) < _ at hσ
        change (contacts K σ : ℝ) ≤ _
        exact hσ.le
    exact (measureReal_mono hsub).trans hclosed
  have hm := hscalar
    ((K.sup (fun x => K.sup (fun y => siteRadius x y)) : ℕ) : ℝ)
    (wilsonColorLaw R) (contacts K) (Nat.cast_nonneg _) hmeas hpos hbad
  simpa only [one_div, Real.rpow_eq_pow] using hm

/-- Whole-set translation yields the source scope with positive universal constants. -/
theorem cofinite_reciprocal_pos_of_open_joint_v3
    (hjoint : (∃ ε : ℝ, 0 < ε ∧
  (∀ (r : ℕ), 10 ^ 30 ≤ r → ∀ (R : RootPair),
    (R.zero ∪ R.one)ᶜ.Finite →
    0 ∈ R.zero →
    (∃ b ∈ R.one, (lattice 2).Adj 0 b) →
    ((lattice 2).induce R.zero).Connected →
    (∃ x ∈ R.zero, 2 * r ≤ siteRadius 0 x) →
    ((lattice 2).induce R.one).Connected →
    (∃ y ∈ R.one, siteRadius 0 y = r) →
    ε ≤ (wilsonColorLaw R).real
      (localContactEvent R.zero 0 (2 * r) ((1 / 8 : ℝ) * Real.log (r : ℝ)))) ∧
  (∃ κ : ℕ, 30 ≤ κ ∧
    ∀ (K : Finset (Site 2)) (γ : Set (Site 2)),
      ((lattice 2).induce (K : Set (Site 2))).Connected →
      0 ∈ K → Disjoint (K : Set (Site 2)) γ →
      ((lattice 2).induce γ).Connected → γᶜ.Finite →
      (∃ b ∈ γ, (lattice 2).Adj 0 b) →
      ∀ (h r : ℕ), 10 ≤ h → h ^ κ ≤ r →
      16 * r ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) →
      ∀ (R : RootPair), (K : Set (Site 2)) ⊆ R.zero →
        R.zero ⊆ (K : Set (Site 2)) ∪ (boxSites h : Set (Site 2)) →
        γ ⊆ R.one →
        ε / 2 ≤ (wilsonColorLaw R).real
          (kContactEvent K (3 * (r : ℝ)) ((1 / 16 : ℝ) * Real.log (r : ℝ)))))) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ K : Finset (Site 2),
    ((lattice 2).induce (K : Set (Site 2))).Connected →
    ∀ γ : Set (Site 2), ((lattice 2).induce γ).Connected →
      γᶜ.Finite → Disjoint (K : Set (Site 2)) γ →
      (∃ k ∈ K, ∃ y ∈ γ, (lattice 2).Adj k y) →
      ∀ R : RootPair, R.zero = (K : Set (Site 2)) → R.one = γ →
        (∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw R) ≤
          C * Real.rpow
            (Real.log (((K.sup (fun x => K.sup (fun y => siteRadius x y)) : ℕ) : ℝ) + 2))
            (-a) := by
  obtain ⟨a, C, ha, hC, horigin⟩ := origin_reciprocal_of_open_joint_v3 hjoint
  refine ⟨a, C, ha, hC, ?_⟩
  intro K hK γ hconn hfinite hd hadj R hzero hone
  obtain ⟨k, hk, b, hb, hkb⟩ := hadj
  let z := -k
  let K' := finiteSet K z
  let γ' : Set (Site 2) := {x | x - z ∈ γ}
  have hK' : ((lattice 2).induce (K' : Set (Site 2))).Connected :=
    connected_translate K z hK
  have hconn' : ((lattice 2).induce γ').Connected := connected_set_translate γ z hconn
  have hfinite' : γ'ᶜ.Finite := cofinite_set_translate γ z hfinite
  have hd' : Disjoint (K' : Set (Site 2)) γ' := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp hd ((mem_finiteSet K z x).mp hx) hy
  have h0' : (0 : Site 2) ∈ K' :=
    Finset.mem_image.mpr ⟨k, hk, add_neg_cancel k⟩
  have hb' : ∃ y ∈ γ', (lattice 2).Adj 0 y := by
    refine ⟨b + z, ?_, ?_⟩
    · change b + z - z ∈ γ
      rwa [add_sub_cancel_right]
    · have hm := (adjacency_add k b z).mpr hkb
      simpa only [z, add_neg_cancel] using hm
  obtain ⟨hzero', hone'⟩ := roots_translate_source R K γ z hzero hone
  have hm := horigin K' hK' γ' hconn' hfinite' hd' h0' hb'
    (roots R z) hzero' hone'
  change (∫ σ, (1 : ℝ) / (contacts (finiteSet K z) σ : ℝ) ∂wilsonColorLaw (roots R z)) ≤
    C * Real.rpow (Real.log
      (((((finiteSet K z).sup (fun x => (finiteSet K z).sup (fun y => siteRadius x y))) : ℕ) : ℝ) + 2)) (-a) at hm
  rwa [reciprocal_expectation_translate, diameter_translate] at hm

/-- Exact frozen cofinite reciprocal formula, conditional only on the entire joint formula. -/
theorem cofinite_reciprocal_of_open_joint_v3
    (hjoint : (∃ ε : ℝ, 0 < ε ∧
  (∀ (r : ℕ), 10 ^ 30 ≤ r → ∀ (R : RootPair),
    (R.zero ∪ R.one)ᶜ.Finite →
    0 ∈ R.zero →
    (∃ b ∈ R.one, (lattice 2).Adj 0 b) →
    ((lattice 2).induce R.zero).Connected →
    (∃ x ∈ R.zero, 2 * r ≤ siteRadius 0 x) →
    ((lattice 2).induce R.one).Connected →
    (∃ y ∈ R.one, siteRadius 0 y = r) →
    ε ≤ (wilsonColorLaw R).real
      (localContactEvent R.zero 0 (2 * r) ((1 / 8 : ℝ) * Real.log (r : ℝ)))) ∧
  (∃ κ : ℕ, 30 ≤ κ ∧
    ∀ (K : Finset (Site 2)) (γ : Set (Site 2)),
      ((lattice 2).induce (K : Set (Site 2))).Connected →
      0 ∈ K → Disjoint (K : Set (Site 2)) γ →
      ((lattice 2).induce γ).Connected → γᶜ.Finite →
      (∃ b ∈ γ, (lattice 2).Adj 0 b) →
      ∀ (h r : ℕ), 10 ≤ h → h ^ κ ≤ r →
      16 * r ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) →
      ∀ (R : RootPair), (K : Set (Site 2)) ⊆ R.zero →
        R.zero ⊆ (K : Set (Site 2)) ∪ (boxSites h : Set (Site 2)) →
        γ ⊆ R.one →
        ε / 2 ≤ (wilsonColorLaw R).real
          (kContactEvent K (3 * (r : ℝ)) ((1 / 16 : ℝ) * Real.log (r : ℝ)))))) :
    ∃ a C : ℝ, 0 < a ∧ ∀ K : Finset (Site 2),
    ((lattice 2).induce (K : Set (Site 2))).Connected →
    ∀ γ : Set (Site 2), ((lattice 2).induce γ).Connected →
      γᶜ.Finite → Disjoint (K : Set (Site 2)) γ →
      (∃ k ∈ K, ∃ y ∈ γ, (lattice 2).Adj k y) →
      ∀ R : RootPair, R.zero = (K : Set (Site 2)) → R.one = γ →
        (∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw R) ≤
          C * Real.rpow
            (Real.log (((K.sup (fun x => K.sup (fun y => siteRadius x y)) : ℕ) : ℝ) + 2))
            (-a) := by
  obtain ⟨a, C, ha, _hC, hbound⟩ := cofinite_reciprocal_pos_of_open_joint_v3 hjoint
  exact ⟨a, C, ha, hbound⟩

end
end FiniteAvalanches.Wilson.Lattice.CofiniteReciprocalAssembly
