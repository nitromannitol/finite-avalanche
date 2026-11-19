import FiniteAvalanches.Support.Plane.LoopPaths
import Mathlib.Topology.Subpath

/-!
# Terminal parametrization of a concatenated path

A concatenation can be reparametrized so that its final path occupies any
specified terminal interval of length at most one half.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- A concatenation can be parametrized with its second path on a prescribed
terminal interval, without changing its range or injectivity. -/
theorem path_trans_reparam_terminal {X : Type*} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z) {a : ℝ}
    (ha : 1 / 2 ≤ a) (ha1 : a < 1)
    (hinj : Function.Injective (p.trans q)) :
    ∃ w : Path x z, Function.Injective w ∧ range w = range (p.trans q) ∧
      ∀ (t : unitInterval) (ht : a ≤ (t : ℝ)),
        w t = q ⟨((t : ℝ) - a) / (1 - a), by
          constructor
          · exact div_nonneg (sub_nonneg.mpr ht) (by linarith)
          · apply (div_le_one (by linarith : 0 < 1 - a)).2
            linarith [t.property.2]⟩ := by
  have ha0 : 0 < a := by linarith
  have hb : 0 < 1 - a := by linarith
  let g : ℝ → ℝ := fun t => max (t / (2 * a)) (1 - (1 - t) / (2 * (1 - a)))
  have hgcont : Continuous g := by
    apply Continuous.max <;> fun_prop
  have hgmono : StrictMono g := by
    intro s t h
    apply max_lt_max
    · exact div_lt_div_of_pos_right h (by positivity)
    · have h' := div_lt_div_of_pos_right (sub_lt_sub_left h 1) (by positivity : 0 < 2 * (1 - a))
      linarith
  have hg0 : g 0 = 0 := by
    dsimp [g]
    rw [max_eq_left]
    · simp
    · have hden : 0 < 2 * (1 - a) := by positivity
      have : (1 : ℝ) ≤ 1 / (2 * (1 - a)) := (le_div_iff₀ hden).2 (by linarith)
      simp only [zero_div, sub_zero]
      linarith
  have hg1 : g 1 = 1 := by
    dsimp [g]
    rw [max_eq_right]
    · simp
    · simp only [sub_self, zero_div, sub_zero]
      exact (div_le_one (by positivity : 0 < 2 * a)).2 (by linarith)
  let f : unitInterval → unitInterval := fun t => ⟨g t, by
    constructor
    · rw [← hg0]
      exact hgmono.monotone t.property.1
    · rw [← hg1]
      exact hgmono.monotone t.property.2⟩
  have hfcont : Continuous f := (hgcont.comp continuous_subtype_val).subtype_mk _
  have hf0 : f 0 = 0 := Subtype.ext hg0
  have hf1 : f 1 = 1 := Subtype.ext hg1
  have hfinj : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    exact hgmono.injective (congrArg Subtype.val h)
  let w := (p.trans q).reparam f hfcont hf0 hf1
  refine ⟨w, hinj.comp hfinj, Path.range_reparam _ _ _ _, ?_⟩
  intro t ht
  have hcomp : (t : ℝ) / (2 * a) ≤ 1 - (1 - t) / (2 * (1 - a)) := by
    have hda : 0 < 2 * a := by positivity
    have hdb : 0 < 2 * (1 - a) := by positivity
    field_simp
    nlinarith
  have hft : (f t : ℝ) = 1 - (1 - t) / (2 * (1 - a)) := by
    simp only [f, g, max_eq_right hcomp]
  have hft' : (f t : ℝ) ≥ 1 / 2 := by
    rw [hft]
    have hden : 0 < 2 * (1 - a) := by positivity
    have hdiv : (1 - (t : ℝ)) / (2 * (1 - a)) ≤ 1 / 2 := by
      apply (div_le_iff₀ hden).2
      linarith
    linarith
  change (p.trans q) (f t) = _
  rw [Path.trans_apply]
  split_ifs with h
  · have heq : (f t : ℝ) = 1 / 2 := le_antisymm h hft'
    have ht' : (t : ℝ) = a := by
      rw [hft] at heq
      have hden : 0 < 2 * (1 - a) := by positivity
      have := (div_eq_iff hden.ne').1 (by linarith : (1 - (t : ℝ)) / (2 * (1 - a)) = 1 / 2)
      nlinarith
    convert p.target.trans q.source.symm using 1 <;> congr 1 <;>
      apply Subtype.ext <;> dsimp <;> first | simp [ht'] | linarith
  · congr 1
    apply Subtype.ext
    dsimp
    rw [hft]
    field_simp
    ring

/-- A retained terminal subpath can be traversed at twice its original speed. -/
theorem path_trans_subpath_reparam_terminal {X : Type*} [TopologicalSpace X]
    {x y z : X} (q : Path y z) (u : unitInterval) (hu : u ≠ 1)
    (p : Path x (q u)) (hinj : Function.Injective (p.trans (q.subpath u 1))) :
    ∃ w : Path x (q 1), Function.Injective w ∧
      range w = range (p.trans (q.subpath u 1)) ∧
      ∀ (t : unitInterval) (ht : ((u : ℝ) + 1) / 2 ≤ (t : ℝ)),
        w t = q ⟨2 * (t : ℝ) - 1, by
          constructor
          · have := u.property.1
            linarith
          · linarith [t.property.2]⟩ := by
  have hu1 : (u : ℝ) < 1 := lt_of_le_of_ne u.property.2
    (fun h => hu (Subtype.ext h))
  obtain ⟨w, hw, hwrange, hwt⟩ := path_trans_reparam_terminal p (q.subpath u 1)
    (a := ((u : ℝ) + 1) / 2) (by linarith [u.property.1]) (by linarith) hinj
  refine ⟨w, hw, hwrange, ?_⟩
  intro t ht
  rw [hwt t ht]
  change q (Set.Icc.convexComb u 1 _) = q _
  congr 1
  apply Subtype.ext
  simp only [Set.Icc.coe_convexComb]
  dsimp
  have hne : (1 : ℝ) - u ≠ 0 := by linarith
  have hden : (1 : ℝ) - ((u : ℝ) + 1) / 2 = (1 - (u : ℝ)) / 2 := by ring
  rw [hden]
  field_simp [hne]
  <;> ring

end FiniteAvalanches.Electrical.StatementGeometry
