import FiniteAvalanches.Needle.Sharp.Edges
import FiniteAvalanches.Needle.Sharp.WindowEnergy
import FiniteAvalanches.Needle.Sharp.Subadditivity

set_option autoImplicit false
namespace Needle107RootBudget
open LatticeProb FiniteAvalanches.Needle FiniteAvalanches.Sandpile.FiniteWired
open Needle107Edges
open scoped BigOperators Classical

noncomputable def rootWindow (N : ℕ) (S : Finset (Active N)) : Finset (Point × Fin 2) :=
  S.biUnion fun x => Finset.univ.biUnion fun i : Fin 2 =>
    {(site x, i), (site x-unit i, i)}

lemma card_rootWindow (N : ℕ) (S : Finset (Active N)) :
    (rootWindow N S).card ≤ 4*S.card := by
  unfold rootWindow
  calc
    _ ≤ ∑ x ∈ S, (Finset.univ.biUnion fun i : Fin 2 =>
        {(site x, i), (site x-unit i, i)}).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ S, 4 := by
      apply Finset.sum_le_sum
      intro x _
      calc _ ≤ ∑ i : Fin 2, ({(site x, i), (site x-unit i, i)} :
            Finset (Point × Fin 2)).card := Finset.card_biUnion_le
           _ ≤ ∑ _i : Fin 2, 2 := Finset.sum_le_sum fun _ _ => Finset.card_le_two
           _ = 4 := by norm_num
    _ = _ := by rw [Finset.sum_const, smul_eq_mul]; omega

noncomputable def indicator (N : ℕ) (S : Finset (Active N)) (x : Point) : ℝ :=
  if x ∈ S.image site then 0 else 1

noncomputable def indicatorWire (N : ℕ) (S : Finset (Active N)) : Vertex N → ℝ
  | none => 1
  | some x => indicator N S (site x)

lemma indicator_exterior (N : ℕ) (S : Finset (Active N)) (y : Point)
    (hy : ¬inBox N y) : indicator N S y = 1 := by
  rw [indicator, if_neg]
  rintro hh
  obtain ⟨x, _, he⟩ := Finset.mem_image.mp hh
  exact hy (he ▸ site_inBox N x)

lemma indicator_edge_square (N : ℕ) (S : Finset (Active N)) (e : Edge N) :
    (indicatorWire N S (endpoints e).1-indicatorWire N S (endpoints e).2)^2 =
      (indicator N S (key N e).1-indicator N S ((key N e).1+unit (key N e).2))^2 := by
  cases e with
  | inl e =>
    change (indicator N S (site e.val.1)-indicator N S (site e.val.2))^2 = _
    rw [e.property.choose_spec]
    rfl
  | inr e =>
    rcases e with ⟨⟨x, i, b⟩, he⟩
    cases b
    · have ht := indicator_exterior N S (site x-unit i) (exit_base_outside N x i he)
      change (indicator N S (site x)-1)^2 =
        (indicator N S (site x-unit i)-indicator N S (site x-unit i+unit i))^2
      rw [sub_add_cancel, ht, sub_sq_comm]
    · have ht := indicator_exterior N S (site x+unit i) (exit_top_outside N x i he)
      change (indicator N S (site x)-1)^2 =
        (indicator N S (site x)-indicator N S (site x+unit i))^2
      rw [ht]

lemma indicator_edge_le (N : ℕ) (S : Finset (Active N)) (e : Edge N) :
    (indicatorWire N S (endpoints e).1-indicatorWire N S (endpoints e).2)^2 ≤
      if key N e ∈ rootWindow N S then 1 else 0 := by
  rw [indicator_edge_square]
  by_cases he : key N e ∈ rootWindow N S
  · rw [if_pos he]
    unfold indicator
    split <;> split <;> norm_num
  · rw [if_neg he]
    have hleft : (key N e).1 ∉ S.image site := by
      rintro hx
      obtain ⟨x, hx, hh⟩ := Finset.mem_image.mp hx
      apply he
      exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_biUnion.mpr
        ⟨(key N e).2, Finset.mem_univ _, Finset.mem_insert.mpr (Or.inl (by
          exact Prod.ext (show (key N e).1 = site x from hh.symm) rfl))⟩⟩
    have hright : (key N e).1+unit (key N e).2 ∉ S.image site := by
      rintro hx
      obtain ⟨x, hx, hh⟩ := Finset.mem_image.mp hx
      apply he
      exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_biUnion.mpr
        ⟨(key N e).2, Finset.mem_univ _, Finset.mem_insert.mpr (Or.inr
          (Finset.mem_singleton.mpr (by
            refine Prod.ext ?_ rfl
            rw [hh, add_sub_cancel_right])))⟩⟩
    rw [indicator, if_neg hleft, indicator, if_neg hright, sub_self, zero_pow (by decide)]

/-- The elementary four-copy budget, used for the source's four shallow vertices. -/
theorem wiredConductance_le_four_card (N : ℕ) (S : Finset (Active N)) :
    wiredConductance N S ≤ 4*(S.card : ℝ) := by
  refine (wiredConductance_le_trial N S (indicatorWire N S) rfl ?_).trans ?_
  · intro x hx
    exact if_pos (Finset.mem_image_of_mem site hx)
  · have he := Needle107WindowEnergy.energy_le_card_window
      (fun e : Edge N => (endpoints e).1) (fun e => (endpoints e).2)
      (indicatorWire N S) (key N) (key_injective N) (rootWindow N S) 1
      (by norm_num) (indicator_edge_le N S)
    have hc : ((rootWindow N S).card : ℝ) ≤ 4*(S.card : ℝ) := by
      exact_mod_cast card_rootWindow N S
    rw [mul_one] at he
    exact he.trans hc

end Needle107RootBudget
