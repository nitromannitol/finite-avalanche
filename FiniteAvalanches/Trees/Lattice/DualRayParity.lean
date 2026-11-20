import FiniteAvalanches.Trees.Lattice.Dual
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Interval.Set.Infinite

/-! Ray-crossing parity for finite even sets of dual edges of `ℤ²`.

Dual sites are named as in `dualField`: the dual site `y` is the face whose lower-left
corner is the primal site `y`, so the dual edge `{y, y + e₁}` crosses the primal edge
`{y + e₁, y + e₁ + e₀}`.

For a finite set `D` of dual lattice edges, `rayParity D x` is the parity of the number
of edges of `D` crossed by the horizontal ray from the primal site `x` to the right.
When every dual site meets an even number of edges of `D`, a primal lattice edge has
endpoints of different parity exactly when its dual edge lies in `D`
(`rayParity_add_of_adj`), and only finitely many sites have odd parity
(`rayParity_support_finite`). This is the discrete Jordan curve theorem for even
subgraphs of the square lattice. -/

set_option autoImplicit false

namespace FiniteAvalanches.Trees.Lattice
open LatticeProb
open scoped Classical

noncomputable section

/-- The dual lattice edge crossing a primal lattice edge, inverse to the naming of `dualField`. -/
def dualEdgeOf (f : LatticeEdge) : LatticeEdge :=
  edgeEquiv (dualBaseInv (edgeEquiv.symm f))

theorem dualField_dualEdgeOf (ω : EdgeField) (f : LatticeEdge) :
    dualField ω (dualEdgeOf f) = !ω f := by
  simp only [dualField, dualEdgeOf, Equiv.symm_apply_apply, dualBase_right_inv,
    Equiv.apply_symm_apply]

theorem dualEdgeOf_injective : Function.Injective dualEdgeOf := by
  intro f g h
  have h' := congrArg (fun d => edgeEquiv (dualBase (edgeEquiv.symm d))) h
  simpa only [dualEdgeOf, Equiv.symm_apply_apply, dualBase_right_inv,
    Equiv.apply_symm_apply] using h'

private theorem edgeEquiv_symm_baseEdge (p : Site 2 × Fin 2) :
    edgeEquiv.symm (baseEdge p) = p :=
  edgeEquiv.symm_apply_apply p

theorem dualEdgeOf_baseEdge_zero (y : Site 2) :
    (dualEdgeOf (baseEdge (y, 0))).val = s(y - unit 1, y) := by
  simp only [dualEdgeOf, edgeEquiv_symm_baseEdge, dualBaseInv]
  change s(y - unit (1 - 0), y - unit (1 - 0) + unit (1 - 0)) = s(y - unit 1, y)
  rw [sub_zero, sub_add_cancel]

theorem dualEdgeOf_baseEdge_one (y : Site 2) :
    (dualEdgeOf (baseEdge (y, 1))).val = s(y - unit 0, y) := by
  simp only [dualEdgeOf, edgeEquiv_symm_baseEdge, dualBaseInv]
  change s(y - unit (1 - 1), y - unit (1 - 1) + unit (1 - 1)) = s(y - unit 0, y)
  rw [sub_self, sub_add_cancel]

private theorem site_ext {x y : Site 2} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  funext i
  fin_cases i
  · exact h0
  · exact h1

@[simp] private theorem unit_zero_apply_zero : (unit 0 : Site 2) 0 = 1 := by
  simp [unit]

@[simp] private theorem unit_zero_apply_one : (unit 0 : Site 2) 1 = 0 := by
  simp [unit]

@[simp] private theorem unit_one_apply_zero : (unit 1 : Site 2) 0 = 0 := by
  simp [unit]

@[simp] private theorem unit_one_apply_one : (unit 1 : Site 2) 1 = 1 := by
  simp [unit]

/-- `d` is the dual edge crossing the primal edge `{z, z + e₀}` for a site `z` on the
closed horizontal ray from `x` to the right. -/
def IsRayEdge (x : Site 2) (d : Sym2 (Site 2)) : Prop :=
  ∃ z : Site 2, z 1 = x 1 ∧ x 0 ≤ z 0 ∧ d = s(z - unit 1, z)

/-- Parity of the number of edges of `D` crossed by the horizontal ray from `x`. -/
def rayParity (D : Finset (Sym2 (Site 2))) (x : Site 2) : ZMod 2 :=
  ∑ d ∈ D, if IsRayEdge x d then 1 else 0

/-- A site of the closed horizontal ray from `x` to the right. -/
def OnRay (x v : Site 2) : Prop := v 1 = x 1 ∧ x 0 ≤ v 0

theorem isRayEdge_iff_succ (x : Site 2) (d : Sym2 (Site 2)) :
    IsRayEdge x d ↔ IsRayEdge (x + unit 0) d ∨ d = s(x - unit 1, x) := by
  constructor
  · rintro ⟨z, h1, h0, rfl⟩
    rcases eq_or_lt_of_le h0 with h | h
    · right
      rw [site_ext h.symm h1]
    · left
      exact ⟨z, by simp [h1], by simp; omega, rfl⟩
  · rintro (⟨z, h1, h0, rfl⟩ | rfl)
    · exact ⟨z, by simpa using h1, by simp at h0; omega, rfl⟩
    · exact ⟨x, rfl, le_rfl, rfl⟩

theorem not_isRayEdge_succ_self (x : Site 2) :
    ¬ IsRayEdge (x + unit 0) s(x - unit 1, x) := by
  rintro ⟨z, -, h0, h⟩
  rcases Sym2.eq_iff.mp h with ⟨-, h'⟩ | ⟨h', -⟩
  · rw [← h'] at h0
    simp at h0
  · have := congrFun h' 0
    simp at h0 this
    omega

/-- Moving the ray start one step to the right removes exactly the first crossing. -/
theorem rayParity_eq_succ (D : Finset (Sym2 (Site 2))) (x : Site 2) :
    rayParity D x = rayParity D (x + unit 0) + if s(x - unit 1, x) ∈ D then 1 else 0 := by
  have hpt : ∀ d : Sym2 (Site 2), (if IsRayEdge x d then (1 : ZMod 2) else 0) =
      (if IsRayEdge (x + unit 0) d then 1 else 0) + if d = s(x - unit 1, x) then 1 else 0 := by
    intro d
    by_cases hd : d = s(x - unit 1, x)
    · subst hd
      simp [not_isRayEdge_succ_self, (isRayEdge_iff_succ x _).mpr (Or.inr rfl)]
    · simp [isRayEdge_iff_succ x d, hd]
  unfold rayParity
  rw [Finset.sum_congr rfl fun d _ => hpt d, Finset.sum_add_distrib, Finset.sum_ite_eq']

private theorem isRayEdge_horizontal (x z : Site 2) :
    ¬ IsRayEdge x s(z, z + unit 0) := by
  rintro ⟨w, -, -, h⟩
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have a := congrFun h1 1
    have b := congrFun h2 1
    simp at a b
    omega
  · have a := congrFun h1 1
    have b := congrFun h2 1
    simp at a b
    omega

private theorem isRayEdge_vertical (x z : Site 2) :
    IsRayEdge x s(z, z + unit 1) ↔ z 1 + 1 = x 1 ∧ x 0 ≤ z 0 := by
  constructor
  · rintro ⟨w, hw1, hw0, h⟩
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have a := congrFun h2 0
      have b := congrFun h2 1
      simp at a b
      omega
    · have a := congrFun h1 1
      have b := congrFun h2 1
      simp at a b
      omega
  · rintro ⟨h1, h0⟩
    refine ⟨z + unit 1, by simpa using h1, by simpa using h0, ?_⟩
    rw [add_sub_cancel_right]

private theorem horizontal_ne_vertical (x z : Site 2) :
    s(z, z + unit 1) ≠ s(x - unit 0, x) := by
  intro h
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have a := congrFun h1 1
    have b := congrFun h2 1
    simp at a b
    omega
  · have a := congrFun h1 0
    have b := congrFun h2 0
    have c := congrFun h1 1
    have d := congrFun h2 1
    simp at a b c d
    omega

private theorem horizontal_eq_iff (x z : Site 2) :
    s(z, z + unit 0) = s(x - unit 0, x) ↔ z 1 = x 1 ∧ z 0 + 1 = x 0 := by
  constructor
  · intro h
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have a := congrFun h2 0
      have b := congrFun h2 1
      simp at a b
      omega
    · have a := congrFun h1 0
      have b := congrFun h2 0
      simp at a b
      omega
  · rintro ⟨h1, h0⟩
    have hz : z = x - unit 0 := site_ext (by simp; omega) (by simp [h1])
    rw [hz, sub_add_cancel]

/-- The local count behind the vertical step: an edge from `z` meets the ray from `x`
in as many sites, modulo two, as it contributes to the two adjacent ray parities and
to the dual edge `{x - e₀, x}`. -/
private theorem edge_onRay_count (x z : Site 2) (i : Fin 2) :
    ((if OnRay x z then 1 else 0) + (if OnRay x (z + unit i) then 1 else 0) : ZMod 2) =
      (if IsRayEdge x s(z, z + unit i) then 1 else 0) +
        (if IsRayEdge (x + unit 1) s(z, z + unit i) then 1 else 0) +
        (if s(z, z + unit i) = s(x - unit 0, x) then 1 else 0) := by
  fin_cases i
  · change ((if OnRay x z then 1 else 0) + (if OnRay x (z + unit 0) then 1 else 0) : ZMod 2) =
      (if IsRayEdge x s(z, z + unit 0) then 1 else 0) +
        (if IsRayEdge (x + unit 1) s(z, z + unit 0) then 1 else 0) +
        (if s(z, z + unit 0) = s(x - unit 0, x) then 1 else 0)
    rw [if_neg (isRayEdge_horizontal x z), if_neg (isRayEdge_horizontal _ z)]
    simp only [horizontal_eq_iff, OnRay, Pi.add_apply, unit_zero_apply_zero,
      unit_zero_apply_one, add_zero]
    by_cases h1 : z 1 = x 1
    · by_cases h0 : x 0 ≤ z 0
      · rw [if_pos ⟨h1, h0⟩, if_pos ⟨h1, by omega⟩, if_neg (by omega)]
        decide
      · by_cases h0' : x 0 ≤ z 0 + 1
        · rw [if_neg (by tauto), if_pos ⟨h1, h0'⟩, if_pos ⟨h1, by omega⟩]
        · rw [if_neg (by tauto), if_neg (by tauto), if_neg (by omega)]
    · rw [if_neg (by tauto), if_neg (by tauto), if_neg (by tauto)]
  · change ((if OnRay x z then 1 else 0) + (if OnRay x (z + unit 1) then 1 else 0) : ZMod 2) =
      (if IsRayEdge x s(z, z + unit 1) then 1 else 0) +
        (if IsRayEdge (x + unit 1) s(z, z + unit 1) then 1 else 0) +
        (if s(z, z + unit 1) = s(x - unit 0, x) then 1 else 0)
    rw [if_neg (horizontal_ne_vertical x z)]
    simp only [isRayEdge_vertical, OnRay, Pi.add_apply,
      unit_one_apply_zero, unit_one_apply_one, add_zero, add_left_inj]
    rw [add_comm]
    split_ifs <;> rfl

/-- Summing the local counts over an even set: the vertical step of the ray parity. -/
theorem rayParity_add_up (D : Finset (Sym2 (Site 2)))
    (hlat : ∀ d ∈ D, ∃ z : Site 2, ∃ i : Fin 2, d = s(z, z + unit i))
    (heven : ∀ v : Site 2, ∑ d ∈ D, (if v ∈ d then 1 else 0 : ZMod 2) = 0) (x : Site 2) :
    rayParity D x + rayParity D (x + unit 1) + (if s(x - unit 0, x) ∈ D then 1 else 0) = 0 := by
  set W : Finset (Site 2) := (D.biUnion Sym2.toFinset).filter (OnRay x) with hW
  have hsum : ∑ d ∈ D, ∑ v ∈ W, (if v ∈ d then 1 else 0 : ZMod 2) = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun v _ => heven v
  have hmemW : ∀ d ∈ D, ∀ v ∈ d, (v ∈ W ↔ OnRay x v) := by
    intro d hd v hv
    rw [hW, Finset.mem_filter, Finset.mem_biUnion]
    exact ⟨fun h => h.2, fun h => ⟨⟨d, hd, Sym2.mem_toFinset.mpr hv⟩, h⟩⟩
  have hedge : ∀ d ∈ D, ∑ v ∈ W, (if v ∈ d then 1 else 0 : ZMod 2) =
      (if IsRayEdge x d then 1 else 0) + (if IsRayEdge (x + unit 1) d then 1 else 0) +
        (if d = s(x - unit 0, x) then 1 else 0) := by
    intro d hd
    obtain ⟨z, i, rfl⟩ := hlat d hd
    have hne : z ≠ z + unit i := by
      intro h
      have := congrArg (· - z) h
      simp only [sub_self, add_sub_cancel_left] at this
      exact unit_ne_zero i this.symm
    have hsplit : ∀ v : Site 2, (if v ∈ s(z, z + unit i) then (1 : ZMod 2) else 0) =
        (if v = z then 1 else 0) + (if v = z + unit i then 1 else 0) := by
      intro v
      by_cases hz : v = z
      · subst hz
        simp [hne]
      · by_cases hz' : v = z + unit i
        · subst hz'
          simp [hz]
        · simp [hz, hz', Sym2.mem_iff]
    rw [Finset.sum_congr rfl fun v _ => hsplit v, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq', ← edge_onRay_count]
    rw [if_congr (hmemW _ hd z (Sym2.mem_mk_left _ _)) rfl rfl,
      if_congr (hmemW _ hd _ (Sym2.mem_mk_right _ _)) rfl rfl]
  rw [Finset.sum_congr rfl hedge, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq'] at hsum
  exact hsum

private theorem zmod_two_add_add_eq_zero {a b c : ZMod 2} (h : a + b + c = 0) : a + b = c := by
  revert a b c
  decide

/-- The discrete Jordan property of the ray parity: a primal lattice edge separates the
parity exactly when its dual edge lies in the even set `D`. -/
theorem rayParity_add_of_adj (D : Finset (Sym2 (Site 2)))
    (hlat : ∀ d ∈ D, ∃ z : Site 2, ∃ i : Fin 2, d = s(z, z + unit i))
    (heven : ∀ v : Site 2, ∑ d ∈ D, (if v ∈ d then 1 else 0 : ZMod 2) = 0)
    {a b : Site 2} (h : (lattice 2).Adj a b) :
    rayParity D a + rayParity D b =
      if (dualEdgeOf ⟨s(a, b), h⟩).val ∈ D then 1 else 0 := by
  have key : ∀ (y : Site 2) (i : Fin 2),
      rayParity D y + rayParity D (y + unit i) =
        if (dualEdgeOf (baseEdge (y, i))).val ∈ D then 1 else 0 := by
    intro y i
    fin_cases i
    · change rayParity D y + rayParity D (y + unit 0) =
        if (dualEdgeOf (baseEdge (y, 0))).val ∈ D then 1 else 0
      rw [dualEdgeOf_baseEdge_zero, rayParity_eq_succ D y]
      generalize rayParity D (y + unit 0) = t
      generalize (if s(y - unit 1, y) ∈ D then (1 : ZMod 2) else 0) = c
      revert t c
      decide
    · change rayParity D y + rayParity D (y + unit 1) =
        if (dualEdgeOf (baseEdge (y, 1))).val ∈ D then 1 else 0
      rw [dualEdgeOf_baseEdge_one]
      exact zmod_two_add_add_eq_zero (rayParity_add_up D hlat heven y)
  obtain ⟨i, hb | ha⟩ := h
  · subst hb
    exact key a i
  · subst ha
    have he : ∀ hh : s(b + unit i, b) ∈ (lattice 2).edgeSet,
        (⟨s(b + unit i, b), hh⟩ : LatticeEdge) = baseEdge (b, i) :=
      fun _ => Subtype.ext Sym2.eq_swap
    rw [he, add_comm]
    exact key b i

/-- Only finitely many sites have odd ray parity. -/
theorem rayParity_support_finite (D : Finset (Sym2 (Site 2)))
    (hlat : ∀ d ∈ D, ∃ z : Site 2, ∃ i : Fin 2, d = s(z, z + unit i))
    (heven : ∀ v : Site 2, ∑ d ∈ D, (if v ∈ d then 1 else 0 : ZMod 2) = 0) :
    {x : Site 2 | rayParity D x ≠ 0}.Finite := by
  set V : Finset (Site 2) := D.biUnion Sym2.toFinset with hV
  set M : ℤ := ∑ v ∈ V, (|v 0| + |v 1|) with hM
  have hbound : ∀ v ∈ V, |v 0| ≤ M ∧ |v 1| ≤ M := by
    intro v hv
    have hle : |v 0| + |v 1| ≤ M :=
      Finset.single_le_sum (f := fun v : Site 2 => |v 0| + |v 1|)
        (fun w _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hv
    exact ⟨by linarith [abs_nonneg (v 1)], by linarith [abs_nonneg (v 0)]⟩
  have hmemV : ∀ d ∈ D, ∀ v ∈ d, v ∈ V := fun d hd v hv =>
    Finset.mem_biUnion.mpr ⟨d, hd, Sym2.mem_toFinset.mpr hv⟩
  have hray : ∀ x, rayParity D x ≠ 0 → ∃ z ∈ V, z 1 = x 1 ∧ x 0 ≤ z 0 := by
    intro x hx
    by_contra hno
    push Not at hno
    apply hx
    refine Finset.sum_eq_zero fun d hd => if_neg ?_
    rintro ⟨z, h1, h0, rfl⟩
    exact (hno z (hmemV _ hd z (Sym2.mem_mk_right _ _)) h1).not_ge h0
  have hzero_high : ∀ x : Site 2, M < |x 1| → rayParity D x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨z, hz, h1, -⟩ := hray x hne
    have := (hbound z hz).2
    rw [h1] at this
    omega
  have hleft : ∀ n : ℕ, ∀ x : Site 2, x 0 < -M → M < x 1 + n → rayParity D x = 0 := by
    intro n
    induction n with
    | zero =>
      intro x _ hx1
      exact hzero_high x (lt_of_lt_of_le (by simpa using hx1) (le_abs_self _))
    | succ n ih =>
      intro x hx0 hx1
      have hnot : s(x - unit 0, x) ∉ D := by
        intro hd
        have := (hbound x (hmemV _ hd x (Sym2.mem_mk_right _ _))).1
        rw [abs_le] at this
        omega
      have hup := rayParity_add_up D hlat heven x
      rw [if_neg hnot, add_zero] at hup
      have heq : rayParity D x = rayParity D (x + unit 1) := by
        generalize rayParity D x = t at hup ⊢
        generalize rayParity D (x + unit 1) = t' at hup ⊢
        revert t t'
        decide
      rw [heq]
      exact ih _ (by simpa using hx0) (by simp; push_cast at hx1; omega)
  refine (Set.finite_Icc (fun _ : Fin 2 => -M) (fun _ => M)).subset ?_
  intro x hx
  have hx' : rayParity D x ≠ 0 := hx
  obtain ⟨z, hz, h1, h0⟩ := hray x hx'
  have hzb := hbound z hz
  have hx1 : |x 1| ≤ M := by rw [← h1]; exact hzb.2
  have hx0 : -M ≤ x 0 := by
    by_contra hlt
    push Not at hlt
    refine hx' (hleft (M - x 1 + 1).toNat x hlt ?_)
    rw [abs_le] at hx1
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  have hx0' : x 0 ≤ M := le_trans h0 (abs_le.mp hzb.1).2
  rw [abs_le] at hx1
  rw [Set.mem_Icc, Pi.le_def, Pi.le_def]
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i
  · exact hx0
  · exact hx1.1
  · exact hx0'
  · exact hx1.2

end

end FiniteAvalanches.Trees.Lattice
