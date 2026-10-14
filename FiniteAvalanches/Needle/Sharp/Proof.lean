import FiniteAvalanches.Needle.Sharp.Runs
import FiniteAvalanches.Needle.Sharp.RootBudget
import FiniteAvalanches.Needle.Sharp.Numeric
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false
namespace Needle107Target
open LatticeProb FiniteAvalanches.Needle FiniteAvalanches.Sandpile.FiniteWired
open Needle107Path Needle107Runs Needle107RootBudget Needle107SquareEnergy Needle107Subadditivity
open scoped BigOperators Classical

noncomputable def central (h : ℕ) : Finset (Active (2*h)) :=
  Finset.univ.filter fun x => site x ∈ box 2 h

noncomputable def shallow (h L : ℕ) (p : InBoxVertices h L) : Finset (Fin (L+1)) :=
  Finset.univ.filter fun t => 2*h-radius (p.val t) ≤ 1

noncomputable def layer (h L k : ℕ) (p : InBoxVertices h L) : Finset (Fin (L+1)) :=
  Finset.univ.filter fun t =>
    (2^k : ℕ) ≤ 2*h-radius (p.val t) ∧
    2*h-radius (p.val t) < (2^(k+1) : ℕ) ∧ h < radius (p.val t)

lemma layer_scale (k : ℕ) (hk : 1 ≤ k) :
    2*2^(k-1) = (2^k : ℕ) ∧ 4*2^(k-1) = (2^(k+1) : ℕ) := by
  have he : k = (k-1)+1 := by omega
  rw [he, Nat.add_sub_cancel, pow_succ, pow_succ]
  constructor <;> ring

lemma central_budget (h : ℕ) (hh : 10 ≤ h) : wiredConductance (2*h) (central h) ≤ 16 := by
  refine inner_square_conductance_le (2*h) h (by omega) 0 (by simp [radius]) _ ?_
  intro x hx
  have hhx := (Finset.mem_filter.mp hx).2
  simpa only [linf, sub_zero] using (mem_box_iff _ _).mp hhx

lemma shallow_budget (h L : ℕ) (p : InBoxVertices h L)
    (hspan : ∀ s t, |(s.val : ℤ)-t.val| ≤ 2*|radius (p.val s)-radius (p.val t)|+1) :
    wiredConductance (2*h) (roots h L p (shallow h L p)) ≤ 16 := by
  have hc : (shallow h L p).card ≤ 4 := by
    apply card_of_index_span L 3
    intro s hs t ht
    have hsδ := (Finset.mem_filter.mp hs).2
    have htδ := (Finset.mem_filter.mp ht).2
    have hsR := (mem_box_iff _ _).mp (p.property s)
    have htR := (mem_box_iff _ _).mp (p.property t)
    have hh := hspan s t
    have hd : |radius (p.val s)-radius (p.val t)| ≤ 1 := by
      rw [abs_le]
      omega
    exact hh.trans (by omega)
  have hc' : (roots h L p (shallow h L p)).card ≤ 4 := (roots_card_le _ _ _ _).trans hc
  exact (wiredConductance_le_four_card _ _).trans (by exact_mod_cast Nat.mul_le_mul_left 4 hc')

lemma layer_budget (h L : ℕ) (p : InBoxVertices h L)
    (hstep : ∀ t : Fin L, (lattice 2).Adj (p.val ⟨t.val, by omega⟩)
      (p.val ⟨t.val+1, by omega⟩))
    (hspan : ∀ s t, |(s.val : ℤ)-t.val| ≤ 2*|radius (p.val s)-radius (p.val t)|+1)
    (k : ℕ) (hk : 1 ≤ k) :
    wiredConductance (2*h) (roots h L p (layer h L k p)) ≤ 64 := by
  set r : ℕ := 2^(k-1) with hrEq
  clear_value r
  have hr : 1 ≤ r := hrEq ▸ Nat.one_le_pow (k-1) 2 (by decide)
  have h2 : 2*r = (2^k : ℕ) := by rw [hrEq]; exact (layer_scale k hk).1
  have h4 : 4*r = (2^(k+1) : ℕ) := by rw [hrEq]; exact (layer_scale k hk).2
  have h2' : 2*(r : ℤ) = ((2^k : ℕ) : ℤ) := by exact_mod_cast h2
  have h4' : 4*(r : ℤ) = ((2^(k+1) : ℕ) : ℤ) := by exact_mod_cast h4
  refine roots_run_budget h L r hr p hstep (layer h L k p) ?_ ?_
  · intro s hs t ht
    obtain ⟨hs1, hs2, _⟩ := (Finset.mem_filter.mp hs).2
    obtain ⟨ht1, ht2, _⟩ := (Finset.mem_filter.mp ht).2
    rw [← h2'] at hs1 ht1
    rw [← h4'] at hs2 ht2
    have hh := hspan s t
    have hd : |radius (p.val s)-radius (p.val t)| ≤ 2*(r : ℤ)-1 := by
      rw [abs_le]
      omega
    exact hh.trans (by omega)
  · intro t ht
    have hδ := (Finset.mem_filter.mp ht).2.1
    rw [← h2'] at hδ
    omega

lemma roots_cover (h L : ℕ) (p : InBoxVertices h L) :
    zeroVertices h L p = central h ∪ roots h L p (shallow h L p) ∪
      (Finset.Icc 1 (Nat.log2 h)).biUnion (fun k => roots h L p (layer h L k p)) := by
  ext x
  simp only [zeroVertices, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_biUnion]
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hb | hp
    · exact Or.inl (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_boxPoints _ _).mp hb⟩))
    · obtain ⟨t, _, hxt⟩ := Finset.mem_image.mp hp
      by_cases htbox : p.val t ∈ box 2 h
      · exact Or.inl (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxt ▸ htbox⟩))
      · have hR := (mem_box_iff _ _).mp (p.property t)
        have hnR : h < radius (p.val t) := by rw [mem_box_iff] at htbox; omega
        let d := (2*h-radius (p.val t)).toNat
        have hd : (d : ℤ) = 2*h-radius (p.val t) := Int.toNat_of_nonneg (by omega)
        by_cases hd1 : d ≤ 1
        · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, t,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩, hxt.symm⟩))
        · let k := Nat.log2 d
          have hd0 : d ≠ 0 := by omega
          have hkd : 1 ≤ k := by
            rw [show k = Nat.log 2 d from Nat.log2_eq_log_two]
            exact Nat.le_log_of_pow_le (by decide) (by norm_num; omega)
          have hkh : k ≤ Nat.log2 h := by
            change Nat.log2 d ≤ Nat.log2 h
            simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right (b := 2) (by omega : d ≤ h)
          have hp1 : (2^k : ℕ) ≤ d := by
            rw [show k = Nat.log 2 d from Nat.log2_eq_log_two]
            exact Nat.pow_log_le_self 2 hd0
          have hp2 : d < (2^(k+1) : ℕ) := by
            rw [show k = Nat.log 2 d from Nat.log2_eq_log_two]
            exact Nat.lt_pow_succ_log_self (by decide) d
          exact Or.inr ⟨k, Finset.mem_Icc.mpr ⟨hkd, hkh⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, t,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
                exact ⟨by omega, by omega, hnR⟩⟩, hxt.symm⟩⟩
  · rintro (hx | ⟨k, _, hx⟩)
    · rcases hx with hx | hx
      · exact Finset.mem_union_left _ ((mem_boxPoints _ _).mpr (Finset.mem_filter.mp hx).2)
      · obtain ⟨t, _, hxt⟩ := (Finset.mem_filter.mp hx).2
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, hxt.symm⟩)
    · obtain ⟨t, _, hxt⟩ := (Finset.mem_filter.mp hx).2
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, hxt.symm⟩)

lemma path_target_budget (h L : ℕ) (hh : 10 ≤ h) (p : InBoxVertices h L)
    (hstep : ∀ t : Fin L, (lattice 2).Adj (p.val ⟨t.val, by omega⟩)
      (p.val ⟨t.val+1, by omega⟩))
    (hspan : ∀ s t, |(s.val : ℤ)-t.val| ≤ 2*|radius (p.val s)-radius (p.val t)|+1) :
    wiredConductance (2*h) (zeroVertices h L p) ≤ 107*Real.log h := by
  have hcard : (Finset.Icc 1 (Nat.log2 h)).card = Nat.log2 h := by rw [Nat.card_Icc]; omega
  have hlayer : wiredConductance (2*h)
      ((Finset.Icc 1 (Nat.log2 h)).biUnion (fun k => roots h L p (layer h L k p))) ≤
      64*(Nat.log2 h : ℝ) := by
    calc _ ≤ ∑ k ∈ Finset.Icc 1 (Nat.log2 h),
            wiredConductance (2*h) (roots h L p (layer h L k p)) :=
              wiredConductance_biUnion_le _ _ _
         _ ≤ ∑ _k ∈ Finset.Icc 1 (Nat.log2 h), (64 : ℝ) :=
              Finset.sum_le_sum fun k hk => layer_budget h L p hstep hspan k (Finset.mem_Icc.mp hk).1
         _ = _ := by rw [Finset.sum_const, hcard, nsmul_eq_mul]; ring
  have hbound : wiredConductance (2*h) (zeroVertices h L p) ≤ 32+64*(Nat.log2 h : ℝ) := by
    rw [roots_cover]
    have hU1 := wiredConductance_union_le (2*h) (central h) (roots h L p (shallow h L p))
    have hU2 := wiredConductance_union_le (2*h) (central h ∪ roots h L p (shallow h L p))
      ((Finset.Icc 1 (Nat.log2 h)).biUnion (fun k => roots h L p (layer h L k p)))
    linarith only [hU1, hU2, central_budget h hh, shallow_budget h L p hspan, hlayer]
  have hlog : (Nat.log2 h : ℝ) ≤ Real.log h / Real.log 2 := Real.log2_le_logb h
  exact hbound.trans ((by linarith only [hlog] :
    32+64*(Nat.log2 h : ℝ) ≤ 32+64*(Real.log h/Real.log 2)).trans
      (Needle107Numeric.source_dyadic_bound h hh))

                                                                        
theorem connected_set_conductance_107 :
    ∀ h : ℕ, 10 ≤ h → ∀ w : Point, radius w = 2 * h →
    ∃ Z : Finset Point, ((lattice 2).induce (Z : Set Point)).Connected ∧
      (Z : Set Point) ⊆ box 2 (2 * h) ∧ box 2 h ⊆ (Z : Set Point) ∧ w ∈ Z ∧
      wiredConductance (2 * h)
        (Finset.univ.filter (fun x : Active (2 * h) => site x ∈ Z)) ≤
          107 * Real.log h := by
  intro h hh w hw
  obtain ⟨L, p, hb, he, ha, hs⟩ := exists_quantitative_path h w hw
  have hwend : w ∈ target h L p.val := by
    rw [← he]
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  refine ⟨target h L p.val,
    FiniteAvalanches.Needle.ConnectedSetApplication.induced_connected_of_lattice_connected _
      ⟨w, hwend⟩ (target_connected h L p.val hb ha), ?_, ?_, hwend,
    path_target_budget h L hh p ha hs⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hbox | hpath
    · have hr := (mem_box_iff x h).mp ((mem_boxPoints h x).mp hbox)
      exact (mem_box_iff x (2*h)).mpr (by omega)
    · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hpath
      exact p.property t
  · exact fun x hx => Finset.mem_union_left _ ((mem_boxPoints h x).mpr hx)

end Needle107Target
