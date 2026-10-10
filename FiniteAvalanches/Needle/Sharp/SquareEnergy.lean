import FiniteAvalanches.Needle.Sharp.Square
import FiniteAvalanches.Needle.Sharp.WindowEnergy
import FiniteAvalanches.Needle.Conductance

set_option autoImplicit false
namespace Needle107SquareEnergy
open LatticeProb FiniteAvalanches.Needle FiniteAvalanches.Sandpile.FiniteWired
open Needle107Edges Needle107Square
open scoped BigOperators Classical

noncomputable def wire (N r : ℕ) (c : Point) : Vertex N → ℝ
  | none => 1
  | some x => tent r (radius (site x-c))

lemma exterior_tent_one (N r : ℕ) (hr : 1 ≤ r) (c y : Point)
    (hc : radius c + 2*r-1 ≤ N) (hy : ¬inBox N y) :
    tent r (radius (y-c)) = 1 := by
  apply tent_one r hr
  by_contra hh
  have hR := radius_le_radius_add y c
  have hb : radius y ≤ N := by omega
  exact hy ((inBox_iff N y).mpr ((mem_box_iff y N).mpr hb))

lemma radius_neighbor (x y c : Point) (hxy : (lattice 2).Adj x y) :
    |radius (x-c)-radius (y-c)| ≤ 1 := by
  have h1 := linf_triangle x y c
  have h2 := linf_triangle y x c
  have he := radius_sub_neighbor hxy
  have he' := radius_sub_neighbor hxy.symm
  dsimp only [linf] at h1 h2
  rw [he] at h1
  rw [he'] at h2
  rw [abs_le]
  omega

lemma edge_wire_square (N r : ℕ) (hr : 1 ≤ r) (c : Point)
    (hc : radius c + 2*r-1 ≤ N) (e : Edge N) :
    (wire N r c (endpoints e).1 - wire N r c (endpoints e).2)^2 =
      (tent r (radius ((key N e).1-c)) -
        tent r (radius ((key N e).1+unit (key N e).2-c)))^2 := by
  cases e with
  | inl e =>
    change (tent r (radius (site e.val.1-c)) - tent r (radius (site e.val.2-c)))^2 = _
    rw [e.property.choose_spec]
    rfl
  | inr e =>
    rcases e with ⟨⟨x, i, b⟩, he⟩
    cases b
    · have hy : ¬inBox N (site x-unit i) := exit_base_outside N x i he
      have hT := exterior_tent_one N r hr c (site x-unit i) hc hy
      have hsum : site x - unit i + unit i = site x := sub_add_cancel _ _
      change (tent r (radius (site x-c))-1)^2 =
        (tent r (radius (site x-unit i-c))-
          tent r (radius (site x-unit i+unit i-c)))^2
      rw [hsum, hT, sub_sq_comm]
    · have hy : ¬inBox N (site x+unit i) := exit_top_outside N x i he
      have hT := exterior_tent_one N r hr c (site x+unit i) hc hy
      change (tent r (radius (site x-c))-1)^2 =
        (tent r (radius (site x-c))-tent r (radius (site x+unit i-c)))^2
      rw [hT]

lemma edge_wire_le_window (N r : ℕ) (hr : 1 ≤ r) (c : Point)
    (hc : radius c + 2*r-1 ≤ N) (e : Edge N) :
    (wire N r c (endpoints e).1-wire N r c (endpoints e).2)^2 ≤
      if key N e ∈ window r c then (1/(r : ℝ))^2 else 0 := by
  rw [edge_wire_square N r hr c hc e]
  by_cases he : key N e ∈ window r c
  · rw [if_pos he]
    have hb := tent_lipschitz r hr _ _
      (radius_neighbor _ _ c (key_adj N e))
    have hp : 0 ≤ 1/(r : ℝ) := by positivity
    nlinarith only [sq_abs (tent r (radius ((key N e).1-c))-
      tent r (radius ((key N e).1+unit (key N e).2-c))),
      mul_nonneg (abs_nonneg (tent r (radius ((key N e).1-c))-
        tent r (radius ((key N e).1+unit (key N e).2-c)))) (sub_nonneg.mpr hb),
      mul_nonneg hp (sub_nonneg.mpr hb)]
  · rw [if_neg he]
    have hh : tent r (radius ((key N e).1-c)) =
        tent r (radius ((key N e).1+unit (key N e).2-c)) := by
      by_contra hne
      exact he (changed_mem_window r hr c _ _ hne)
    rw [hh, sub_self, zero_pow (by decide)]

/-- A translated cutoff costs at most 16, with every original copied edge retained. -/
theorem wire_energy_le_sixteen (N r : ℕ) (hr : 1 ≤ r) (c : Point)
    (hc : radius c + 2*r-1 ≤ N) :
    FiniteAvalanches.Electrical.energy (fun e : Edge N => (endpoints e).1)
      (fun e => (endpoints e).2) (wire N r c) ≤ 16 := by
  have hp : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hcard : ((window r c).card : ℝ) ≤ 16*(r : ℝ)*r := by
    exact_mod_cast card_window r hr c
  calc
    _ ≤ ((window r c).card : ℝ) * (1/(r : ℝ))^2 :=
      Needle107WindowEnergy.energy_le_card_window
        (fun e : Edge N => (endpoints e).1) (fun e => (endpoints e).2)
        (wire N r c) (key N) (key_injective N) (window r c) ((1/(r : ℝ))^2)
        (sq_nonneg _) (edge_wire_le_window N r hr c hc)
    _ ≤ (16*(r : ℝ)*r) * (1/(r : ℝ))^2 :=
      mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ = 16 := by field_simp

/-- Actual copied conductance of every set inside the translated inner square. -/
theorem inner_square_conductance_le (N r : ℕ) (hr : 1 ≤ r) (c : Point)
    (hc : radius c + 2*r-1 ≤ N) (S : Finset (Active N))
    (hS : ∀ x ∈ S, linf (site x) c ≤ r) : wiredConductance N S ≤ 16 := by
  refine (wiredConductance_le_trial N S (wire N r c) rfl ?_).trans
    (wire_energy_le_sixteen N r hr c hc)
  intro x hx
  exact tent_zero r _ (hS x hx)

end Needle107SquareEnergy
