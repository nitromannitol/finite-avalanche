import FiniteAvalanches.Needle.Geometry
import Mathlib.Logic.Function.Iterate

/-! The literal largest-coordinate step, with coordinate zero chosen in a tie. -/

namespace FiniteAvalanches.Needle
open LatticeProb

private def inwardCoordinate (a : ℤ) : ℤ :=
  if 0 < a then a - 1 else if a < 0 then a + 1 else 0

private theorem abs_inwardCoordinate (a : ℤ) :
    |inwardCoordinate a| = max 0 (|a| - 1) := by
  unfold inwardCoordinate
  split
  · rename_i ha
    rw [abs_of_nonneg (by omega), abs_of_pos ha, max_eq_right (by omega)]
  · rename_i ha
    split
    · rename_i hb
      rw [abs_of_nonpos (by omega), abs_of_neg hb, max_eq_right (by omega)]
      omega
    · rename_i hb
      have hz : a = 0 := by omega
      subst a
      norm_num

/-- Move toward zero in a largest absolute coordinate, choosing the first in a tie. -/
def needleGreedyStep (x : Point) : Point :=
  if |x 1| ≤ |x 0| then ![inwardCoordinate (x 0), x 1]
  else ![x 0, inwardCoordinate (x 1)]

/-- Integer L1 distance, used only to bound the finite greedy clock. -/
def needleGreedyMass (x : Point) : ℕ := (|x 0| + |x 1|).toNat

theorem needle_greedy_mass_cast (x : Point) :
    (needleGreedyMass x : ℤ) = |x 0| + |x 1| :=
  Int.toNat_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))

theorem needle_greedy_mass_eq_zero_iff (x : Point) : needleGreedyMass x = 0 ↔ x = 0 := by
  have hm := needle_greedy_mass_cast x
  have h0 := abs_nonneg (x 0)
  have h1 := abs_nonneg (x 1)
  constructor
  · intro hz
    rw [hz] at hm
    have hx0 : x 0 = 0 := abs_eq_zero.mp (by omega)
    have hx1 : x 1 = 0 := abs_eq_zero.mp (by omega)
    funext i
    fin_cases i <;> dsimp <;> assumption
  · rintro rfl
    simp [needleGreedyMass]

theorem needle_greedy_radius_le (x : Point) : radius (needleGreedyStep x) ≤ radius x := by
  have h0 := abs_nonneg (x 0)
  have h1 := abs_nonneg (x 1)
  unfold needleGreedyStep
  split <;> dsimp only [radius, Matrix.cons_val_zero, Matrix.cons_val_one]
  · rw [abs_inwardCoordinate]
    omega
  · rw [abs_inwardCoordinate]
    omega

theorem needle_greedy_mass_step (x : Point) :
    needleGreedyMass (needleGreedyStep x) = needleGreedyMass x - 1 := by
  have h0 := abs_nonneg (x 0)
  have h1 := abs_nonneg (x 1)
  have hm := needle_greedy_mass_cast x
  unfold needleGreedyStep
  split
  · have hs := needle_greedy_mass_cast (![inwardCoordinate (x 0), x 1])
    dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hs
    rw [abs_inwardCoordinate] at hs
    omega
  · have hs := needle_greedy_mass_cast (![x 0, inwardCoordinate (x 1)])
    dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hs
    rw [abs_inwardCoordinate] at hs
    omega

theorem needle_greedy_adj (x : Point) (hx : 0 < radius x) :
    (lattice 2).Adj x (needleGreedyStep x) := by
  unfold needleGreedyStep
  split
  · rename_i hle
    have hx0 : 0 < |x 0| := by dsimp only [radius] at hx; omega
    by_cases hp : 0 < x 0
    · refine ⟨0, Or.inr ?_⟩
      funext i
      fin_cases i <;> dsimp [inwardCoordinate, unit] <;> simp [hp]
    · have hn : x 0 < 0 := by rw [abs_eq_max_neg] at hx0; omega
      refine ⟨0, Or.inl ?_⟩
      funext i
      fin_cases i <;> dsimp [inwardCoordinate, unit] <;> simp [hp, hn]
  · rename_i hle
    have hx1 : 0 < |x 1| := by dsimp only [radius] at hx; omega
    by_cases hp : 0 < x 1
    · refine ⟨1, Or.inr ?_⟩
      funext i
      fin_cases i <;> dsimp [inwardCoordinate, unit] <;> simp [hp]
    · have hn : x 1 < 0 := by rw [abs_eq_max_neg] at hx1; omega
      refine ⟨1, Or.inl ?_⟩
      funext i
      fin_cases i <;> dsimp [inwardCoordinate, unit] <;> simp [hp, hn]

theorem needle_greedy_radius_drop_two (x : Point) (hx : 0 < radius x) :
    radius (needleGreedyStep (needleGreedyStep x)) ≤ radius x - 1 := by
  have h0 := abs_nonneg (x 0)
  have h1 := abs_nonneg (x 1)
  by_cases hcase : |x 1| ≤ |x 0|
  · have hg : needleGreedyStep x = ![inwardCoordinate (x 0), x 1] :=
      if_pos hcase
    rw [hg, needleGreedyStep]
    dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    split <;> dsimp only [radius, Matrix.cons_val_zero, Matrix.cons_val_one] at *
    all_goals simp only [abs_inwardCoordinate] at *
    all_goals omega
  · have hg : needleGreedyStep x = ![x 0, inwardCoordinate (x 1)] :=
      if_neg hcase
    rw [hg, needleGreedyStep]
    dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    split <;> dsimp only [radius, Matrix.cons_val_zero, Matrix.cons_val_one] at *
    all_goals simp only [abs_inwardCoordinate] at *
    all_goals omega

/-- The infinite clock whose finite first-entry prefix is the source path. -/
def needleGreedyOrbit (w : Point) (t : ℕ) : Point := needleGreedyStep^[t] w

theorem needle_greedy_orbit_succ (w : Point) (t : ℕ) :
    needleGreedyOrbit w (t + 1) = needleGreedyStep (needleGreedyOrbit w t) :=
  Function.iterate_succ_apply' _ _ _

theorem needle_greedy_orbit_mass (w : Point) (t : ℕ) :
    needleGreedyMass (needleGreedyOrbit w t) = needleGreedyMass w - t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [needle_greedy_orbit_succ, needle_greedy_mass_step, ih]
    omega

theorem needle_greedy_orbit_radius_antitone (w : Point) :
    Antitone (fun t => radius (needleGreedyOrbit w t)) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [needle_greedy_orbit_succ]
  exact needle_greedy_radius_le _

theorem needle_greedy_orbit_reaches_zero (w : Point) :
    needleGreedyOrbit w (needleGreedyMass w) = 0 := by
  apply (needle_greedy_mass_eq_zero_iff _).mp
  rw [needle_greedy_orbit_mass, Nat.sub_self]

end FiniteAvalanches.Needle
