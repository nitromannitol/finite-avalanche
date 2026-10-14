import FiniteAvalanches.Needle.Direct.GreedyStep
import FiniteAvalanches.Needle.Sharp.Path

/-! The first-entry prefix of the literal greedy trajectory. -/

namespace FiniteAvalanches.Needle
open LatticeProb

theorem needle_greedy_mass_le_twice_radius (w : Point) :
    (needleGreedyMass w : ℤ) ≤ 2 * radius w := by
  rw [needle_greedy_mass_cast, radius]
  omega

/-- Before the finite greedy clock ends, time is controlled by the radial decrease. -/
theorem needle_greedy_time_radius (w : Point) (t : ℕ) (ht : t ≤ needleGreedyMass w) :
    (t : ℤ) ≤ 2 * (radius w - radius (needleGreedyOrbit w t)) + 1 := by
  revert ht
  induction t using Nat.twoStepInduction with
  | zero => intro _; simp [needleGreedyOrbit]
  | one =>
    intro _
    have hr := needle_greedy_orbit_radius_antitone w (show 0 ≤ (1 : ℕ) by omega)
    change radius (needleGreedyOrbit w 1) ≤ radius w at hr
    omega
  | more n hn _ =>
    intro ht
    have ih := hn (by omega : n ≤ needleGreedyMass w)
    have hmass := needle_greedy_mass_le_twice_radius w
    have hp := radius_nonneg (needleGreedyOrbit w n)
    by_cases hz : radius (needleGreedyOrbit w n) = 0
    · have hr := needle_greedy_orbit_radius_antitone w (show n ≤ n + 2 by omega)
      change radius (needleGreedyOrbit w (n + 2)) ≤ radius (needleGreedyOrbit w n) at hr
      rw [hz] at hr
      have hn0 := radius_nonneg (needleGreedyOrbit w (n + 2))
      omega
    · have hd := needle_greedy_radius_drop_two (needleGreedyOrbit w n) (by omega)
      have he : needleGreedyOrbit w (n + 2) =
          needleGreedyStep (needleGreedyStep (needleGreedyOrbit w n)) := by
        rw [show n + 2 = (n + 1) + 1 by omega,
          needle_greedy_orbit_succ, needle_greedy_orbit_succ]
      rw [← he] at hd
      omega

private theorem exists_greedy_entrance (h : ℕ) (w : Point) :
    ∃ t : ℕ, radius (needleGreedyOrbit w t) ≤ h := by
  refine ⟨needleGreedyMass w, ?_⟩
  rw [needle_greedy_orbit_reaches_zero]
  simp only [radius, Pi.zero_apply, abs_zero, max_self]
  exact Nat.cast_nonneg h

/-- The first time at which the specified greedy trajectory enters the inner box. -/
noncomputable def needleGreedyEntrance (h : ℕ) (w : Point) : ℕ :=
  Nat.find (exists_greedy_entrance h w)

theorem needle_greedy_entrance_mem (h : ℕ) (w : Point) :
    needleGreedyOrbit w (needleGreedyEntrance h w) ∈ box 2 h :=
  (mem_box_iff _ h).mpr (Nat.find_spec (exists_greedy_entrance h w))

theorem needle_greedy_before_entrance (h : ℕ) (w : Point) (t : ℕ)
    (ht : t < needleGreedyEntrance h w) : (h : ℤ) < radius (needleGreedyOrbit w t) :=
  lt_of_not_ge (Nat.find_min (exists_greedy_entrance h w) ht)

theorem needle_greedy_entrance_le_mass (h : ℕ) (w : Point) :
    needleGreedyEntrance h w ≤ needleGreedyMass w := by
  apply Nat.find_min'
  rw [needle_greedy_orbit_reaches_zero]
  simp only [radius, Pi.zero_apply, abs_zero, max_self]
  exact Nat.cast_nonneg h

/-- The finite nearest-neighbor family, ordered from the boundary point toward the box. -/
noncomputable def needleGreedyPath (h : ℕ) (w : Point) :
    Fin (needleGreedyEntrance h w + 1) → Point :=
  fun t => needleGreedyOrbit w t.val

theorem needle_greedy_path_start (h : ℕ) (w : Point) :
    needleGreedyPath h w ⟨0, by omega⟩ = w := rfl

theorem needle_greedy_path_end (h : ℕ) (w : Point) :
    needleGreedyPath h w ⟨needleGreedyEntrance h w, by omega⟩ ∈ box 2 h :=
  needle_greedy_entrance_mem h w

theorem needle_greedy_path_rule (h : ℕ) (w : Point)
    (t : Fin (needleGreedyEntrance h w)) :
    needleGreedyPath h w ⟨t.val + 1, by omega⟩ =
      needleGreedyStep (needleGreedyPath h w ⟨t.val, by omega⟩) :=
  needle_greedy_orbit_succ w t.val

theorem needle_greedy_path_adj (h : ℕ) (w : Point)
    (t : Fin (needleGreedyEntrance h w)) :
    (lattice 2).Adj (needleGreedyPath h w ⟨t.val, by omega⟩)
      (needleGreedyPath h w ⟨t.val + 1, by omega⟩) := by
  rw [needle_greedy_path_rule]
  apply needle_greedy_adj
  have hr := needle_greedy_before_entrance h w t.val t.isLt
  have hn : (0 : ℤ) ≤ h := Nat.cast_nonneg h
  exact hn.trans_lt hr

theorem needle_greedy_path_injective (h : ℕ) (w : Point) :
    Function.Injective (needleGreedyPath h w) := by
  intro s t he
  have hm := congrArg needleGreedyMass he
  change needleGreedyMass (needleGreedyOrbit w s.val) =
    needleGreedyMass (needleGreedyOrbit w t.val) at hm
  rw [needle_greedy_orbit_mass, needle_greedy_orbit_mass] at hm
  have hs := s.isLt
  have ht := t.isLt
  have hL := needle_greedy_entrance_le_mass h w
  apply Fin.ext
  omega

theorem needle_greedy_path_in_box (h : ℕ) (w : Point) (hw : radius w = 2 * h)
    (t : Fin (needleGreedyEntrance h w + 1)) : needleGreedyPath h w t ∈ box 2 (2 * h) := by
  apply (mem_box_iff _ (2 * h)).mpr
  have hr := needle_greedy_orbit_radius_antitone w (Nat.zero_le t.val)
  change radius (needleGreedyPath h w t) ≤ radius w at hr
  rw [hw] at hr
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hr

theorem needle_greedy_path_time_bound (h : ℕ) (w : Point) (hw : radius w = 2 * h)
    (t : Fin (needleGreedyEntrance h w + 1)) :
    (t.val : ℤ) ≤ 2 * (2 * h - radius (needleGreedyPath h w t)) + 1 := by
  have ht := t.isLt
  have hL := needle_greedy_entrance_le_mass h w
  have hh := needle_greedy_time_radius w t.val (by omega)
  rw [hw] at hh
  exact hh

theorem needle_greedy_path_distance_bound (h : ℕ) (w : Point) (hw : radius w = 2 * h)
    (t : Fin (needleGreedyEntrance h w + 1)) :
    linf (needleGreedyPath h w t) w ≤ 2 * (2 * h - radius (needleGreedyPath h w t)) + 1 := by
  have hd := Needle107Path.path_linf_le_span (needleGreedyEntrance h w)
    (needleGreedyPath h w) (needle_greedy_path_adj h w) ⟨0, by omega⟩ t
  rw [needle_greedy_path_start, linf_comm] at hd
  have hdist : linf (needleGreedyPath h w t) w ≤ (t.val : ℤ) := by
    simpa only [Nat.cast_zero, zero_sub, abs_neg,
      abs_of_nonneg (show (0 : ℤ) ≤ (t.val : ℤ) from Nat.cast_nonneg t.val)] using hd
  exact hdist.trans (needle_greedy_path_time_bound h w hw t)

end FiniteAvalanches.Needle
