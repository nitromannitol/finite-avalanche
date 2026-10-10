import FiniteAvalanches.Wilson.Lattice.CofiniteGlobalContact
import FiniteAvalanches.Wilson.Lattice.PaddedHistoryLocalization
import FiniteAvalanches.Wilson.Lattice.ClosedContactScales

/-! The closed cofinite-root lower tail, retaining the exact shared witnesses. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.CofiniteClosedContact
open LatticeProb FiniteAvalanches Sandpile MeasureTheory
open BatchRestart ConditionalIteration7 ActualContactHistory ActualContactRestriction
open ActualQueryPrefixes ActualLocalizationUnion WarmContactPrefixes WarmContactIteration
open CofiniteRestartGeometry CofiniteHistorySuccess CofiniteContactScales NestedBoxStepThree
open CofiniteGlobalContact PaddedHistoryLocalization ClosedContactScales
open scoped Classical
noncomputable section

/-- For n>=2 only the first tested radius is increased by one. The strict
larger threshold controls the closed source event without excluding a boundary
atom or changing epsilon/kappa. The warm-up and all error radii remain literal. -/
theorem actual_cofinite_global_closed_tail_of_open_joint_v3
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
    ∃ ε : ℝ, 0 < ε ∧
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
      ∃ κ : ℕ, 30 ≤ κ ∧ ∃ D : ℝ, 0 < D ∧
        ∀ (K : Finset (Site 2)) (γ : Set (Site 2))
          (_hK : ((lattice 2).induce (K : Set (Site 2))).Connected)
          (h0 : (0 : Site 2) ∈ K) (hd : Disjoint (K : Set (Site 2)) γ)
          (_hconn : ((lattice 2).induce γ).Connected) (_hfinite : γᶜ.Finite)
          (hb : ∃ b ∈ γ, (lattice 2).Adj 0 b) (n : ℕ),
          1 ≤ n →
          16 * 2 ^ ((6 * κ) ^ (2 * n - 1)) ≤
            K.sup (fun x => K.sup (fun y => siteRadius x y)) →
          (wilsonColorLaw (sourceRoots K γ hd h0 hb)).real
            {σ : ColorField | (contacts K σ : ℝ) ≤
              (1 / 16 : ℝ) * Real.log (2 ^ ((6 * κ) ^ n) : ℕ)} ≤
            (1 - ε / 2) ^ n +
              2 * D * (2 ^ ((6 * κ) ^ (n - 1)) : ℕ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨ε, hε, hlocal, κ, hκ, hstep⟩ := one_step_history_success_of_open_joint_v3 hjoint
  obtain ⟨D₀, hD₀, hexit⟩ := nested_prefix_history_escape
  obtain ⟨Dₚ, hDₚ, hpad⟩ := padded_box_list_history_escape
  let D := D₀ + Dₚ + 1
  have hD : 0 < D := by dsimp only [D]; linarith only [hD₀, hDₚ]
  have hD1 : 1 ≤ D := by dsimp only [D]; linarith only [hD₀, hDₚ]
  have hD₀D : D₀ ≤ D := by dsimp only [D]; linarith only [hDₚ]
  have hDₚD : Dₚ ≤ D := by dsimp only [D]; linarith only [hD₀]
  refine ⟨ε, hε, hlocal, κ, hκ, D, hD, ?_⟩
  intro K γ hK h0 hd hconn hfinite hb n hn hdiam
  let r := sourceScale κ
  let R := sourceRoots K γ hd h0 hb
  have hr : Monotone r := sourceScale_mono κ hκ
  have hp1 : ε / 2 ≤ 1 := by
    have hdiam0 : 16 * r n ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) :=
      (Nat.mul_le_mul_left 16 (hr (by omega : n ≤ 2 * n - 1))).trans hdiam
    have hm := hstep K γ hK h0 hd hconn hfinite hb 10 (r n) (by norm_num)
      (ten_pow_le_sourceScale κ n hκ hn) hdiam0 []
      (fun _ _ => 0) (initialSampler R) rfl (by intro p hp; cases hp)
    change ε / 2 * wilsonRows.real (historyAtom R [] (initialSampler R)) ≤ _ at hm
    rw [historyAtom_initial_nil, probReal_univ, mul_one] at hm
    exact hm.trans measureReal_le_one
  by_cases hn1 : n = 1
  · subst n
    have he := initial_error_ge_one D hD1
    have hq : 0 ≤ 1 - ε / 2 := sub_nonneg.mpr hp1
    change (wilsonColorLaw R).real _ ≤ (1 - ε / 2) ^ 1 +
      2 * D * (sourceScale κ (1 - 1) : ℝ) ^ (-(1 / 2 : ℝ))
    simp only [sourceScale, Nat.sub_self, pow_zero, pow_one, Nat.cast_ofNat]
    exact measureReal_le_one.trans (he.trans (le_add_of_nonneg_left hq))
  have hn2 : 2 ≤ n := by omega
  let s := fun j => r (n - 1 + j)
  let a := fun j => s j + if j = 1 then 1 else 0
  let b := fun i => r (n + i) + if i = 0 then 1 else 0
  let Q := fun j => (boxSites (3 * a j + 1)).toList
  let F := fun i => K.filter (fun x => (siteRadius 0 x : ℝ) ≤ 3 * (b i : ℝ))
  let h := fun i => r (n - 1 + i) ^ 6
  let t := (1 / 16 : ℝ) * Real.log (r n + 1 : ℕ)
  have hs : Monotone s := fun i j hij => hr (Nat.add_le_add_left hij (n - 1))
  have ha (j : ℕ) : a j ≤ s j + 1 := by dsimp only [a]; split_ifs <;> omega
  have hab (i : ℕ) : a (i + 1) = b i := by
    have hidx : n - 1 + (i + 1) = n + i := by omega
    have hi : (i + 1 = 1) ↔ i = 0 := by omega
    simp only [a, b, s, hidx, hi]
  have hcommon (i : ℕ) : r n + 1 ≤ b i := by
    dsimp only [b]
    split_ifs with hi
    · subst i
      simp only [Nat.add_zero]
      exact le_rfl
    · exact (sourceScale_add_one_le_next κ n hκ).trans (hr (by omega : n + 1 ≤ n + i))
  have hdiamstep (i : ℕ) (hi : i < n) :
      16 * b i ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) := by
    apply (Nat.mul_le_mul_left 16 ?_).trans hdiam
    dsimp only [b]
    split_ifs with hz
    · subst i
      simp only [Nat.add_zero]
      exact (sourceScale_add_one_le_next κ n hκ).trans (hr (by omega : n + 1 ≤ 2 * n - 1))
    · simp only [Nat.add_zero]
      exact hr (by omega : n + i ≤ 2 * n - 1)
  have hdiam6 (i : ℕ) (hi : i < n) :
      16 * s i ^ 6 ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) :=
    (Nat.mul_le_mul_left 16 (sourceScale_six_le_diameter_scale κ n (n - 1 + i)
      hκ hn (by omega))).trans hdiam
  have hheights (i : ℕ) : 10 ≤ h i := sourceHeight_ten_le κ (n - 1 + i) hκ
  have hscales (i : ℕ) : h i ^ κ ≤ b i := by
    have he : n - 1 + i + 1 = n + i := by omega
    have hnext : h i ^ κ = r (n + i) := by
      rw [← he]
      exact (sourceScale_succ κ (n - 1 + i)).symm
    rw [hnext]
    exact Nat.le_add_right _ _
  have hsuccess : ∀ i < n, ∀ out : SamplerState,
      (historyAtom R (warmPrefix Q i) out).Nonempty →
      (∀ path ∈ out.history, ∀ j : Fin (path.length + 1),
        path.vertex j ∈ (boxSites (h i) : Set (Site 2))) →
      (ε / 2) * wilsonRows.real (historyAtom R (warmPrefix Q i) out) ≤
        wilsonRows.real (historyAtom R (warmPrefix Q i) out ∩
          continuationContactEvent (initialSampler R) (warmPrefix Q (i + 1)) (F i) t) := by
    intro i hi out hrealized hstay
    obtain ⟨ξ, hξ⟩ := hrealized
    have hm := hstep K γ hK h0 hd hconn hfinite hb (h i) (b i)
      (hheights i) (hscales i) (hdiamstep i hi) (warmPrefix Q i) ξ out hξ hstay
    have ht : t ≤ (1 / 16 : ℝ) * Real.log (b i : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity : (0 : ℝ) < (r n + 1 : ℕ))
        (by exact_mod_cast hcommon i)) (by norm_num)
    have hsub : continuationContactEvent (initialSampler R)
        (warmPrefix Q i ++ (boxSites (3 * b i + 1)).toList) (F i)
          ((1 / 16 : ℝ) * Real.log (b i : ℝ)) ⊆
        continuationContactEvent (initialSampler R) (warmPrefix Q (i + 1)) (F i) t := by
      rintro η ⟨next, hnxt, σ, hσ, hc⟩
      refine ⟨next, ?_, σ, ht.trans hσ, hc⟩
      simpa only [warmPrefix, queryPrefix, Q, hab i] using hnxt
    exact hm.trans (measureReal_mono (Set.inter_subset_inter_right _ hsub))
  have hsurvive := warm_surviving_le_pow R Q F h t (ε / 2) n (by linarith only [hε]) hp1 hsuccess
  have herrors : (∑ i : Fin n, wilsonRows.real (prefixExit R (warmPrefix Q i.val) (h i.val))) ≤
      2 * D * (r (n - 1) : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hpoint (i : Fin n) : wilsonRows.real (prefixExit R (warmPrefix Q i.val) (h i.val)) ≤
        D * (s i.val : ℝ) ^ (-(1 / 2 : ℝ)) := by
      by_cases hi : i.val = 0
      · have hm := hexit K hK h0 R (fun _ hx => hx) s hs 0
          (sourceScale_two_le κ (n - 1 + 0) hκ) (hdiam6 0 (by omega))
        have hm' : wilsonRows (prefixExit R (warmPrefix Q i.val) (h i.val)) ≤
            ENNReal.ofReal (D₀ * (s i.val : ℝ) ^ (-(1 / 2 : ℝ))) := by
          simpa only [hi, warmPrefix, queryPrefix, List.nil_append, Q, a,
            if_neg (by omega : (0 : ℕ) ≠ 1), Nat.add_zero, h, s] using hm
        have hmreal := ENNReal.toReal_mono (by finiteness) hm'
        rw [ENNReal.toReal_ofReal (mul_nonneg hD₀.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))] at hmreal
        exact hmreal.trans (mul_le_mul_of_nonneg_right hD₀D (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      · have hm := hpad K hK h0 R (fun _ hx => hx) (s i.val)
          (sourceScale_two_le κ (n - 1 + i.val) hκ) (hdiam6 i.val i.isLt)
          (warmPrefix Q i.val) (queryPrefix_padded_starts s a hs ha i.val)
        have hmreal := ENNReal.toReal_mono (by finiteness) hm
        rw [ENNReal.toReal_ofReal (mul_nonneg hDₚ.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))] at hmreal
        exact hmreal.trans (mul_le_mul_of_nonneg_right hDₚD (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    calc
      _ ≤ ∑ i : Fin n, D * (s i.val : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Finset.sum_le_sum (fun i _ => hpoint i)
      _ = D * ∑ i : Fin n, (s i.val : ℝ) ^ (-(1 / 2 : ℝ)) := (Finset.mul_sum _ _ _).symm
      _ ≤ D * (2 * (r (n - 1) : ℝ) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (source_error_sum κ n hκ) hD.le
      _ = _ := by ring
  have hglobal := global_low_mass_le_warm_failures R K Q F n t
    (fun _ _ => Finset.filter_subset _ _)
  have hclosed : {σ : ColorField | (contacts K σ : ℝ) ≤ (1 / 16 : ℝ) * Real.log (r n : ℝ)} ⊆
      {σ : ColorField | (contacts K σ : ℝ) < t} :=
    fun _ hσ => hσ.trans_lt (source_threshold_lt_padded κ n hκ)
  exact (measureReal_mono hclosed).trans (hglobal.trans
    ((warm_failures_le_surviving_add_exits R Q F h t n).trans (add_le_add hsurvive herrors)))

end
end FiniteAvalanches.Wilson.Lattice.CofiniteClosedContact
