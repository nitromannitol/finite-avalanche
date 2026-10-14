import FiniteAvalanches.Needle.Direct.TestFunctionEdges
import FiniteAvalanches.Needle.Direct.ShellEdges
import FiniteAvalanches.Needle.Direct.ShellSum
import Mathlib.Algebra.BigOperators.Intervals

/-! Once-counted energy of the clipped quotient on the actual wired box. -/

namespace FiniteAvalanches.Needle
open LatticeProb Sandpile.FiniteWired
open scoped BigOperators Classical

/-- The literal cutoff, with zero at the contracted exterior. -/
noncomputable def needleWiredTest (h : ℕ) (w : Point) : Vertex (2 * h) → ℝ
  | none => 0
  | some x => needleTestFunction h w (site x)

/-- The maximum endpoint distance, retaining the exterior endpoint of every exit copy. -/
noncomputable def needleEdgeRadius (N : ℕ) (w : Point) (e : Edge N) : ℕ :=
  (linf (needleEdgeCharge N w e).1 w).toNat

theorem needle_edge_radius_cast (N : ℕ) (w : Point) (e : Edge N) :
    (needleEdgeRadius N w e : ℤ) = linf (needleEdgeCharge N w e).1 w :=
  Int.toNat_of_nonneg (radius_nonneg _)

private theorem radius_le_of_active (N : ℕ) (x : Active N) : radius (site x) ≤ N :=
  (mem_box_iff _ N).mp ((inBox_iff N _).mp (Needle107Edges.site_inBox N x))

private theorem radius_le_neighbor {x y : Point} (hxy : (lattice 2).Adj x y) :
    radius y ≤ radius x + 1 := by
  have hh := radius_le_radius_add y x
  rw [radius_sub_neighbor hxy.symm] at hh
  omega

private theorem key_has_active_endpoint (N : ℕ) (e : Edge N) :
    radius (Needle107Edges.key N e).1 ≤ N ∨
      radius ((Needle107Edges.key N e).1 + unit (Needle107Edges.key N e).2) ≤ N := by
  cases e with
  | inl e => exact Or.inl (radius_le_of_active N e.val.1)
  | inr e =>
    rcases e with ⟨⟨x, i, b⟩, he⟩
    cases b
    · exact Or.inr (by simpa only [Needle107Edges.key, Bool.false_eq_true,
        if_false, sub_add_cancel] using radius_le_of_active N x)
    · exact Or.inl (radius_le_of_active N x)

theorem needle_edge_radius_bounds (h : ℕ) (w : Point) (hw : radius w = 2 * h)
    (e : Edge (2 * h)) : 1 ≤ needleEdgeRadius (2 * h) w e ∧
      needleEdgeRadius (2 * h) w e ≤ 4 * h + 1 := by
  let q := Needle107Edges.key (2 * h) e
  have ha := Needle107Edges.key_adj (2 * h) e
  have h0 := radius_le_neighbor ha
  have h1 := radius_le_neighbor ha.symm
  have hb : radius q.1 ≤ 2 * (h : ℤ) + 1 ∧
      radius (q.1 + unit q.2) ≤ 2 * (h : ℤ) + 1 := by
    rcases key_has_active_endpoint (2 * h) e with ht | ht
    · constructor <;> dsimp only [q] at * <;> push_cast at ht <;> omega
    · constructor <;> dsimp only [q] at * <;> push_cast at ht <;> omega
  have hd0 := radius_sub_le q.1 w
  have hd1 := radius_sub_le (q.1 + unit q.2) w
  rw [hw] at hd0 hd1
  have ht := radius_sub_le (q.1 - w) (q.1 + unit q.2 - w)
  have he : (q.1 - w) - (q.1 + unit q.2 - w) = q.1 - (q.1 + unit q.2) := by abel
  rw [he, radius_sub_neighbor ha] at ht
  have hm0 := le_max_left (linf q.1 w) (linf (q.1 + unit q.2) w)
  have hm1 := le_max_right (linf q.1 w) (linf (q.1 + unit q.2) w)
  have hr := needle_edge_radius_cast (2 * h) w e
  rw [needleEdgeCharge, needleRadialCharge_radius] at hr
  change (needleEdgeRadius (2 * h) w e : ℤ) =
    max (linf q.1 w) (linf (q.1 + unit q.2) w) at hr
  dsimp only [linf] at hr hm0 hm1
  constructor <;> omega

theorem needle_wired_edge_square (h : ℕ) (w : Point) (e : Edge (2 * h)) :
    (needleWiredTest h w (endpoints e).1 - needleWiredTest h w (endpoints e).2) ^ 2 =
      (needleTestFunction h w (Needle107Edges.key (2 * h) e).1 -
        needleTestFunction h w ((Needle107Edges.key (2 * h) e).1 +
          unit (Needle107Edges.key (2 * h) e).2)) ^ 2 := by
  cases e with
  | inl e =>
    change (needleTestFunction h w (site e.val.1) - needleTestFunction h w (site e.val.2)) ^ 2 = _
    rw [e.property.choose_spec]
    rfl
  | inr e =>
    rcases e with ⟨⟨x, i, b⟩, he⟩
    cases b
    · have hz := needle_test_function_eq_zero_of_outside h w (site x - unit i)
        (fun hm => Needle107Edges.exit_base_outside (2 * h) x i he
          ((inBox_iff (2 * h) _).mpr hm))
      simp only [endpoints, needleWiredTest, Needle107Edges.key, Bool.false_eq_true,
        if_false, sub_add_cancel, hz, sub_zero, zero_sub, neg_sq]
    · have hz := needle_test_function_eq_zero_of_outside h w (site x + unit i)
        (fun hm => Needle107Edges.exit_top_outside (2 * h) x i he
          ((inBox_iff (2 * h) _).mpr hm))
      simp only [endpoints, needleWiredTest, Needle107Edges.key, if_true, hz]

theorem needle_wired_edge_bound (h : ℕ) (w : Point) (hw : radius w = 2 * h)
    (e : Edge (2 * h)) :
    (needleWiredTest h w (endpoints e).1 - needleWiredTest h w (endpoints e).2) ^ 2 ≤
      (6 / (1 + (needleEdgeRadius (2 * h) w e : ℝ))) ^ 2 := by
  rw [needle_wired_edge_square]
  have hh := needle_test_function_edge_bound h w (Needle107Edges.key (2 * h) e).1
    ((Needle107Edges.key (2 * h) e).1 + unit (Needle107Edges.key (2 * h) e).2) hw
    (Needle107Edges.key_adj (2 * h) e)
  have hr := needle_edge_radius_cast (2 * h) w e
  rw [needleEdgeCharge, needleRadialCharge_radius] at hr
  have hr' : (needleEdgeRadius (2 * h) w e : ℝ) =
      max (linf (Needle107Edges.key (2 * h) e).1 w : ℝ)
        (linf ((Needle107Edges.key (2 * h) e).1 +
          unit (Needle107Edges.key (2 * h) e).2) w : ℝ) := by exact_mod_cast hr
  rw [← hr'] at hh
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hh

private theorem card_radius_fiber (N : ℕ) (w : Point) (k : ℕ) (hk : 1 ≤ k) :
    (Finset.univ.filter (fun e : Edge N => needleEdgeRadius N w e = k)).card ≤ 32 * k := by
  have hs : Finset.univ.filter (fun e : Edge N => needleEdgeRadius N w e = k) =
      Finset.univ.filter (fun e : Edge N => linf (needleEdgeCharge N w e).1 w = k) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ← needle_edge_radius_cast, Nat.cast_inj]
  rw [hs]
  exact card_needle_edge_shell_le N w k hk

/-- The source shell sum controls the actual once-counted wired energy. -/
theorem needle_direct_energy_le_shell_sum (h : ℕ) (w : Point) (hw : radius w = 2 * h) :
    Electrical.energy (fun e : Edge (2 * h) => (endpoints e).1)
      (fun e => (endpoints e).2) (needleWiredTest h w) ≤
        1152 * ∑ k ∈ Finset.Icc 1 (4 * h + 1), (k : ℝ) / (((k : ℝ) + 1) ^ 2) := by
  unfold Electrical.energy
  calc
    _ ≤ ∑ e : Edge (2 * h), (6 / (1 + (needleEdgeRadius (2 * h) w e : ℝ))) ^ 2 :=
      Finset.sum_le_sum fun e _ => needle_wired_edge_bound h w hw e
    _ = ∑ k ∈ Finset.Icc 1 (4 * h + 1),
        ((Finset.univ.filter (fun e : Edge (2 * h) => needleEdgeRadius (2 * h) w e = k)).card : ℝ) *
          (6 / (1 + (k : ℝ))) ^ 2 := by
      rw [← Finset.sum_fiberwise_of_maps_to
        (s := Finset.univ) (t := Finset.Icc 1 (4 * h + 1)) (g := needleEdgeRadius (2 * h) w)
        (fun e _ => Finset.mem_Icc.mpr (needle_edge_radius_bounds h w hw e))]
      apply Finset.sum_congr rfl
      intro k _
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro e he
      rw [(Finset.mem_filter.mp he).2]
    _ ≤ ∑ k ∈ Finset.Icc 1 (4 * h + 1), (32 * (k : ℝ)) * (6 / (1 + (k : ℝ))) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact_mod_cast card_radius_fiber (2 * h) w k (Finset.mem_Icc.mp hk).1
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      field_simp
      ring

private theorem shell_sum_eq_shifted_range (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, (k : ℝ) / (((k : ℝ) + 1) ^ 2)) =
      ∑ k ∈ Finset.range n, ((k : ℝ) + 1) / (((k : ℝ) + 2) ^ 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    congr 2
    ring

/-- The incoming cutoff has the shell energy bound with the literal logarithm. -/
theorem needle_direct_energy_le_log (h : ℕ) (w : Point) (hw : radius w = 2 * h) :
    Electrical.energy (fun e : Edge (2 * h) => (endpoints e).1)
      (fun e => (endpoints e).2) (needleWiredTest h w) ≤
        1152 * Real.log (4 * (h : ℝ) + 2) := by
  apply (needle_direct_energy_le_shell_sum h w hw).trans
  rw [shell_sum_eq_shifted_range]
  have hh := mul_le_mul_of_nonneg_left (needle_shell_sum_le_log (4 * h + 1))
    (by norm_num : (0 : ℝ) ≤ 1152)
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    add_assoc, one_add_one_eq_two] using hh

/-- The source's final constant, on the actual copied-edge wired energy. -/
theorem needle_direct_energy_le_log_h (h : ℕ) (hh : 10 ≤ h) (w : Point)
    (hw : radius w = 2 * h) :
    Electrical.energy (fun e : Edge (2 * h) => (endpoints e).1)
      (fun e => (endpoints e).2) (needleWiredTest h w) ≤ 2304 * Real.log (h : ℝ) := by
  have hp : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have h10 : (10 : ℝ) ≤ h := by exact_mod_cast hh
  have hb : 4 * (h : ℝ) + 2 ≤ (h : ℝ) ^ 2 := by nlinarith
  have hl := Real.log_le_log (by positivity : 0 < 4 * (h : ℝ) + 2) hb
  rw [Real.log_pow] at hl
  calc
    _ ≤ 1152 * Real.log (4 * (h : ℝ) + 2) := needle_direct_energy_le_log h w hw
    _ ≤ 1152 * (2 * Real.log (h : ℝ)) :=
      mul_le_mul_of_nonneg_left hl (by norm_num)
    _ = 2304 * Real.log (h : ℝ) := by ring

end FiniteAvalanches.Needle
