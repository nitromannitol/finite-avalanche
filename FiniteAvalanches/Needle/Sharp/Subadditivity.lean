import FiniteAvalanches.Needle.Conductance
import FiniteAvalanches.Electrical.MaximumPrinciple

set_option autoImplicit false
namespace Needle107Subadditivity
open FiniteAvalanches.Needle FiniteAvalanches.Sandpile.FiniteWired
open scoped BigOperators Classical

lemma min_square (a b c d : ℝ) :
    (min a b - min c d)^2 ≤ (a-c)^2 + (b-d)^2 := by
  rcases le_total a b with hab | hba <;> rcases le_total c d with hcd | hdc
  · rw [min_eq_left hab, min_eq_left hcd]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · rw [min_eq_left hab, min_eq_right hdc]
    by_cases had : d ≤ a
    · have hbd : 0 ≤ b-d := by linarith only [had, hab]
      nlinarith only [had, hab, hbd, mul_nonneg (sub_nonneg.mpr had)
        (by linarith only [hab] : 0 ≤ b-a), sq_nonneg (a-c)]
    · have hac : a-d ≤ 0 := by linarith only [had]
      have hca : a-c ≤ a-d := by linarith only [hdc]
      nlinarith only [hac, hca, mul_nonneg (by linarith only [hac] : 0 ≤ d-a)
        (by linarith only [hdc] : 0 ≤ c-d), sq_nonneg (b-d)]
  · rw [min_eq_right hba, min_eq_left hcd]
    by_cases hbc : c ≤ b
    · nlinarith only [hbc, hba, mul_nonneg (sub_nonneg.mpr hbc)
        (by linarith only [hba] : 0 ≤ a-b), sq_nonneg (b-d)]
    · nlinarith only [hbc, hcd, mul_nonneg (by linarith only [hbc] : 0 ≤ c-b)
        (by linarith only [hcd] : 0 ≤ d-c), sq_nonneg (a-c)]
  · rw [min_eq_right hba, min_eq_right hdc]
    exact le_add_of_nonneg_left (sq_nonneg _)

lemma energy_min {V E : Type} [Fintype E] (a b : E → V) (f g : V → ℝ) :
    FiniteAvalanches.Electrical.energy a b (fun v => min (f v) (g v)) ≤
      FiniteAvalanches.Electrical.energy a b f +
        FiniteAvalanches.Electrical.energy a b g := by
  unfold FiniteAvalanches.Electrical.energy
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun e _ => min_square _ _ _ _

lemma voltage_nonneg (N : ℕ) (S : Finset (Active N)) (v : Vertex N) :
    0 ≤ voltage N S v := by
  exact FiniteAvalanches.Electrical.harmonicExtension_nonneg
    (fun e : Edge N => (endpoints e).1) (fun e => (endpoints e).2)
    (terminals N S) (terminals_reachable N S) (fun u => if u = none then 1 else 0)
    (fun u _ => by split <;> norm_num) v

/-- Subadditivity for the actual full copied wired lattice and actual zero roots. -/
theorem wiredConductance_union_le (N : ℕ) (S T : Finset (Active N)) :
    wiredConductance N (S ∪ T) ≤ wiredConductance N S + wiredConductance N T := by
  refine (wiredConductance_le_trial N (S ∪ T)
    (fun v => min (voltage N S v) (voltage N T v)) ?_ ?_).trans
      (energy_min _ _ _ _)
  · rw [(voltage_spec N S).1, (voltage_spec N T).1, min_self]
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rw [(voltage_spec N S).2.1 x hx, min_eq_left (voltage_nonneg N T (some x))]
    · rw [(voltage_spec N T).2.1 x hx, min_eq_right (voltage_nonneg N S (some x))]

lemma wiredConductance_nonneg (N : ℕ) (S : Finset (Active N)) :
    0 ≤ wiredConductance N S := FiniteAvalanches.Electrical.energy_nonneg _ _ _

lemma wiredConductance_empty (N : ℕ) : wiredConductance N ∅ = 0 := by
  apply le_antisymm
  · refine (wiredConductance_le_trial N ∅ (fun _ => 1) rfl (by simp)).trans ?_
    simp only [FiniteAvalanches.Electrical.energy, sub_self]
    norm_num
  · exact wiredConductance_nonneg N ∅

lemma wiredConductance_mono (N : ℕ) (S T : Finset (Active N)) (hST : S ⊆ T) :
    wiredConductance N S ≤ wiredConductance N T := by
  exact wiredConductance_le_trial N S (voltage N T) (voltage_spec N T).1
    (fun x hx => (voltage_spec N T).2.1 x (hST hx))

lemma capacity_biUnion_le {A I : Type} [DecidableEq A] [DecidableEq I]
    (C : Finset A → ℝ) (h0 : C ∅ = 0)
    (hU : ∀ S T, C (S ∪ T) ≤ C S + C T) (F : Finset I) (S : I → Finset A) :
    C (F.biUnion S) ≤ ∑ i ∈ F, C (S i) := by
  induction F using Finset.induction_on with
  | empty => rw [Finset.biUnion_empty, Finset.sum_empty, h0]
  | @insert i F hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    exact (hU (S i) (F.biUnion S)).trans (add_le_add (le_refl (C (S i))) ih)

lemma wiredConductance_biUnion_le {I : Type} [DecidableEq I] (N : ℕ)
    (A : Finset I) (S : I → Finset (Active N)) :
    wiredConductance N (A.biUnion S) ≤ ∑ i ∈ A, wiredConductance N (S i) :=
  capacity_biUnion_le (wiredConductance N) (wiredConductance_empty N)
    (wiredConductance_union_le N) A S

end Needle107Subadditivity
