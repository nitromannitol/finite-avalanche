import FiniteAvalanches.Wilson.Lattice.HittingTimes
import LatticeProb.Walk.Ball
import LatticeProb.Walk.Infinite

set_option autoImplicit false
namespace FiniteAvalanches.External.Beurling
open LatticeProb MeasureTheory FiniteAvalanches.Wilson.Lattice
open scoped Classical ENNReal
noncomputable section

/-- The pinned direction-product law equals the actual round17 walk law. -/
theorem pathLaw_eq_walkLaw : pathLaw 2 = FiniteAvalanches.Wilson.Lattice.walkLaw := by
  have hstep : stepLaw 2 = directionLaw := by
    apply Measure.ext_of_singleton
    intro a
    rw [stepLaw, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton a),
      PMF.uniformOfFintype_apply, directionLaw, FiniteAvalanches.uniformMeasure_apply]
    simp [Nat.card_eq_fintype_card]
  rw [pathLaw, FiniteAvalanches.Wilson.Lattice.walkLaw, hstep]

 theorem wired_step_eq_dirVec (a : FiniteAvalanches.Sandpile.FiniteWired.Direction) :
    FiniteAvalanches.Sandpile.FiniteWired.step a = dirVec a := by
  rcases a with ⟨i, b⟩
  cases b
  · exact (dirVec_eq_neg_unit i).symm
  · exact (dirVec_eq_unit i).symm

 theorem position_sum (x : Site 2) (ω : WalkDriver) (t : ℕ) :
    position x ω t = x + ∑ j ∈ Finset.range t, dirVec (ω j) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [position_succ, ih, wired_step_eq_dirVec, Finset.sum_range_succ]
    abel

 theorem position_translate (x : Site 2) (ω : WalkDriver) (t : ℕ) :
    position x ω t - x = position 0 ω t := by
  rw [position_sum, position_sum]
  simp

 theorem supNorm_eq_siteRadius (x : Site 2) : supNorm x = FiniteAvalanches.siteRadius 0 x := by
  simp [supNorm, FiniteAvalanches.siteRadius]

end
end FiniteAvalanches.External.Beurling

namespace FiniteAvalanches.External.Beurling
open LatticeProb MeasureTheory FiniteAvalanches.Wilson.Lattice
open scoped Classical ENNReal
noncomputable section

def axis (q : ℤ) : Site 2 := ![q, 0]

@[simp] theorem axis_zero : axis 0 = 0 := by ext i; fin_cases i <;> simp [axis]
@[simp] theorem norm_axis (q : ℤ) : euclidNorm (axis q) = |(q : ℝ)| := by
  simp [euclidNorm, axis, Fin.sum_univ_two, Real.sqrt_sq_eq_abs]
@[simp] theorem sup_axis (q : ℤ) : supNorm (axis q) = q.natAbs := by
  simp [supNorm, axis, show (Finset.univ : Finset (Fin 2)) = {0, 1} from by decide]


def annulus (A : Set (Site 2)) (k n : ℕ) : Set (Site 2) :=
  {z | z ∈ A ∧ (k : ℝ) ≤ euclidNorm z ∧ euclidNorm z < n}


def padded (K : Set (Site 2)) (k n : ℕ) : Set (Site 2) :=
  K ∪ {z | euclidNorm z < k ∨ (n : ℝ) ≤ euclidNorm z}

 theorem annulus_padded (K : Set (Site 2)) (k n : ℕ) :
    annulus (padded K k n) k n = annulus K k n := by
  ext z
  simp only [annulus, padded, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨hK | (hl | hu), hk, hn⟩
    · exact ⟨hK, hk, hn⟩
    · exact False.elim (not_lt_of_ge hk hl)
    · exact False.elim (not_lt_of_ge hu hn)
  · rintro ⟨hK, hk, hn⟩
    exact ⟨Or.inl hK, hk, hn⟩

 theorem padded_dense (K : Set (Site 2)) (k n : ℕ)
    (hmid : ∀ j : ℕ, k ≤ j → j < n → ∃ z ∈ K,
      (j : ℝ) ≤ euclidNorm z ∧ euclidNorm z < (j : ℝ) + 1) :
    ∀ j : ℕ, ∃ z ∈ padded K k n,
      (j : ℝ) ≤ euclidNorm z ∧ euclidNorm z < (j : ℝ) + 1 := by
  intro j
  by_cases hjk : j < k
  · refine ⟨axis (j : ℤ), Or.inr (Or.inl ?_), ?_, ?_⟩ <;>
      simp [norm_axis, abs_of_nonneg (show (0 : ℝ) ≤ j from Nat.cast_nonneg j), hjk]
  · by_cases hjn : j < n
    · obtain ⟨z, hz, hl, hu⟩ := hmid j (by omega) hjn
      exact ⟨z, Or.inl hz, hl, hu⟩
    · refine ⟨axis (j : ℤ), Or.inr (Or.inr ?_), ?_, ?_⟩ <;>
        simp [norm_axis, abs_of_nonneg (show (0 : ℝ) ≤ j from Nat.cast_nonneg j), show n ≤ j by omega]


 theorem supNorm_triangle (x y : Site 2) : supNorm (x + y) ≤ supNorm x + supNorm y := by
  apply supNorm_le_iff.mpr
  intro i
  have hx := supNorm_le_iff.mp (le_refl (supNorm x)) i
  have hy := supNorm_le_iff.mp (le_refl (supNorm y)) i
  simpa only [Pi.add_apply, Nat.cast_add] using (abs_add_le (x i) (y i)).trans (add_le_add hx hy)

 theorem translated_square_exit (x y : Site 2) (r H n : ℕ)
    (hx : supNorm x ≤ r) (hy : H < supNorm y) (hn : 2 * n + r ≤ H + 1) :
    2 * (n : ℝ) ≤ euclidNorm (y - x) := by
  have he : y = (y - x) + x := by abel
  have ht := supNorm_triangle (y - x) x
  rw [← he] at ht
  have hd : 2 * n ≤ supNorm (y - x) := by omega
  have hr : 2 * (n : ℝ) ≤ (supNorm (y - x) : ℝ) := by exact_mod_cast hd
  exact hr.trans (supNorm_le_euclidNorm _)

 theorem query_initial_distance (x : Site 2) (r : ℕ) (hx : supNorm x ≤ r) :
    euclidNorm (-x) < (2 * r + 1 : ℕ) := by
  have hs : supNorm (-x) = supNorm x := by simp [supNorm]
  have he := euclidNorm_le_sqrt_mul_supNorm (-x)
  have hsqrt : Real.sqrt (2 : ℝ) ≤ 2 := by norm_num
  have hxr : (supNorm x : ℝ) ≤ (r : ℝ) := by exact_mod_cast hx
  rw [hs] at he
  have hn : 0 ≤ (supNorm x : ℝ) := by positivity
  norm_num only [Nat.cast_ofNat] at he
  have hb : euclidNorm (-x) ≤ 2 * (r : ℝ) :=
    he.trans ((mul_le_mul_of_nonneg_right hsqrt hn).trans (by linarith))
  push_cast
  linarith

 theorem long_range_integer_radii (r H : ℕ) (hH : 8 * r + 8 ≤ H) :
    0 < 2 * r + 1 ∧ 2 * r + 1 < (H - r) / 2 ∧
      2 * ((H - r) / 2) + r ≤ H + 1 ∧
      (H : ℝ) / 4 ≤ (((H - r) / 2 : ℕ) : ℝ) := by
  have hnat : H ≤ 4 * ((H - r) / 2) := by omega
  refine ⟨by omega, by omega, by omega, ?_⟩
  have hreal : (H : ℝ) ≤ 4 * (((H - r) / 2 : ℕ) : ℝ) := by exact_mod_cast hnat
  linarith

 theorem long_range_ratio (r H : ℕ) (hH : 8 * r + 8 ≤ H) :
    ((2 * r + 1 : ℕ) : ℝ) / (((H - r) / 2 : ℕ) : ℝ) ≤ 8 * ((r + 1 : ℕ) : ℝ) / H := by
  obtain ⟨_, hkn, _, hquarter⟩ := long_range_integer_radii r H hH
  have hn : 0 < (((H - r) / 2 : ℕ) : ℝ) := by exact_mod_cast (show 0 < (H - r) / 2 by omega)
  have hHp : 0 < (H : ℝ) := by exact_mod_cast (show 0 < H by omega)
  apply (div_le_div_iff₀ hn hHp).mpr
  push_cast
  nlinarith [show (0 : ℝ) ≤ r from Nat.cast_nonneg r]



end
end FiniteAvalanches.External.Beurling

namespace FiniteAvalanches.BeurlingConnected
open LatticeProb MeasureTheory FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.External.Beurling
open scoped Classical ENNReal
noncomputable section

private theorem norm_sq (u : Site 2) :
    euclidNorm u ^ 2 = ((u 0 : ℤ) : ℝ)^2 + ((u 1 : ℤ) : ℝ)^2 := by
  unfold euclidNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  simp only [Fin.sum_univ_two]

private theorem coord_le (u : Site 2) (i : Fin 2) :
    |((u i : ℤ) : ℝ)| ≤ euclidNorm u := by
  have hi := supNorm_le_iff.mp (le_refl (supNorm u)) i
  have hr : |((u i : ℤ) : ℝ)| ≤ (supNorm u : ℝ) := by exact_mod_cast hi
  exact hr.trans (supNorm_le_euclidNorm u)

private theorem norm_add_unit_le (u : Site 2) (i : Fin 2) :
    euclidNorm (u + unit i) ≤ euclidNorm u + 1 := by
  have hu := norm_sq u
  have hv := norm_sq (u + unit i)
  have hb := (abs_le.mp (coord_le u i)).2
  have hn := euclidNorm_nonneg (u + unit i)
  have hm := euclidNorm_nonneg u
  fin_cases i <;> norm_num [unit] at hv hb hn ⊢ <;> nlinarith

private theorem norm_sub_unit_le (u : Site 2) (i : Fin 2) :
    euclidNorm (u - unit i) ≤ euclidNorm u + 1 := by
  have hu := norm_sq u
  have hv := norm_sq (u - unit i)
  have hb := (abs_le.mp (coord_le u i)).1
  have hn := euclidNorm_nonneg (u - unit i)
  have hm := euclidNorm_nonneg u
  fin_cases i <;> norm_num [unit] at hv hb hn ⊢ <;> nlinarith

/-- One actual nearest-neighbor step changes translated Euclidean radius by at most1. -/
theorem adjacent_norm_le (u v x : Site 2) (ha : (lattice 2).Adj u v) :
    euclidNorm (v - x) ≤ euclidNorm (u - x) + 1 := by
  obtain ⟨i, he | he⟩ := ha
  · have hh : v - x = (u - x) + unit i := by rw [he]; abel
    rw [hh]
    exact norm_add_unit_le _ _
  · have hh : v - x = (u - x) - unit i := by rw [he]; abel
    rw [hh]
    exact norm_sub_unit_le _ _

/-- The shell witness is constructed by recursion on the actual finite lattice walk. -/
theorem walk_shell {K : Set (Site 2)} {u v : K}
    (p : ((lattice 2).induce K).Walk u v) (x : Site 2) (j : ℕ)
    (hu : euclidNorm (u.val - x) < j) (hv : (j : ℝ) ≤ euclidNorm (v.val - x)) :
    ∃ z ∈ K, (j : ℝ) ≤ euclidNorm (z - x) ∧ euclidNorm (z - x) < (j : ℝ) + 1 := by
  induction p with
  | nil => exact False.elim (not_lt_of_ge hv hu)
  | @cons u w v ha p ih =>
    by_cases hw : (j : ℝ) ≤ euclidNorm (w.val - x)
    · refine ⟨w.val, w.property, hw, ?_⟩
      exact lt_of_le_of_lt (adjacent_norm_le u.val w.val x ha) (by linarith)
    · exact ih (lt_of_not_ge hw) hv

/-- Connectedness supplies a finite simple path crossing a Euclidean shell. -/
theorem connected_shell (K : Set (Site 2))
    (hK : ((lattice 2).induce K).Preconnected) (h0 : (0 : Site 2) ∈ K)
    (z : Site 2) (hz : z ∈ K) (x : Site 2) (j : ℕ)
    (hin : euclidNorm (-x) < j) (hout : (j : ℝ) ≤ euclidNorm (z - x)) :
    ∃ y ∈ K, (j : ℝ) ≤ euclidNorm (y - x) ∧ euclidNorm (y - x) < (j : ℝ) + 1 := by
  obtain ⟨p, _⟩ := (hK ⟨0, h0⟩ ⟨z, hz⟩).exists_isPath
  exact walk_shell p x j (by simpa only [zero_sub] using hin) hout

end
end FiniteAvalanches.BeurlingConnected
