import FiniteAvalanches.External.ArcStraightening
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.ArcCollapse
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source

def ramp (x : ℝ) : ℝ := min x 0 + max (x - 1) 0

def collapseSegment (z : Plane) : Plane := (ramp z.1 + |z.2| * z.1, z.2)

theorem ramp_mono : Monotone ramp := by
  intro x y h
  exact add_le_add (min_le_min_right 0 h) (max_le_max_right 0 (sub_le_sub_right h 1))

theorem ramp_zero (x : ℝ) : ramp x = 0 ↔ x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold ramp
  by_cases h0 : x ≤ 0
  · rw [min_eq_left h0, max_eq_right (by linarith)]
    constructor
    · intro h
      constructor <;> linarith
    · intro h
      linarith [h.1]
  · rw [min_eq_right (le_of_lt (lt_of_not_ge h0))]
    by_cases h1 : x ≤ 1
    · rw [max_eq_right (by linarith)]
      constructor
      · intro _
        exact ⟨le_of_lt (lt_of_not_ge h0), h1⟩
      · intro _
        norm_num
    · rw [max_eq_left (by linarith)]
      constructor
      · intro h
        constructor <;> linarith
      · intro h
        linarith [h.2]

theorem ramp_equal (x y : ℝ) (h : ramp x = ramp y) :
    x = y ∨ (x ∈ Set.Icc (0 : ℝ) 1 ∧ y ∈ Set.Icc (0 : ℝ) 1) := by
  by_cases he : x = y
  · exact Or.inl he
  have aux (a b : ℝ) (hab : a < b) (hr : ramp a = ramp b) :
      a ∈ Set.Icc (0 : ℝ) 1 ∧ b ∈ Set.Icc (0 : ℝ) 1 := by
    have ha : 0 ≤ a := by
      by_contra h0
      have ha0 : a < 0 := lt_of_not_ge h0
      have hbm : a < min b 0 := lt_min hab ha0
      have ham : min a 0 = a := min_eq_left ha0.le
      have hamax : max (a - 1) 0 = 0 := max_eq_right (by linarith)
      have hbmax : 0 ≤ max (b - 1) 0 := le_max_right _ _
      dsimp [ramp] at hr
      rw [ham, hamax] at hr
      linarith
    have hb : b ≤ 1 := by
      by_contra h1
      have hb1 : 1 < b := lt_of_not_ge h1
      have hbmin : min b 0 = 0 := min_eq_right (by linarith)
      have hbmax : max (b - 1) 0 = b - 1 := max_eq_left (by linarith)
      have hamax : max (a - 1) 0 < b - 1 := max_lt (by linarith) (by linarith)
      have hamin : min a 0 ≤ 0 := min_le_right _ _
      dsimp [ramp] at hr
      rw [hbmin, hbmax] at hr
      linarith
    exact ⟨⟨ha, hab.le.trans hb⟩, ⟨ha.trans hab.le, hb⟩⟩
  rcases lt_or_gt_of_ne he with hxy | hyx
  · exact Or.inr (aux x y hxy h)
  · exact Or.inr (aux y x hyx h.symm).symm

theorem collapseSegment_continuous : Continuous collapseSegment := by
  unfold collapseSegment ramp
  fun_prop

theorem collapseSegment_equal (x y : Plane) :
    collapseSegment x = collapseSegment y ↔ x = y ∨
      (x ∈ Set.range (fun t : ArcParameter => (t.val, (0 : ℝ))) ∧
       y ∈ Set.range (fun t : ArcParameter => (t.val, (0 : ℝ)))) := by
  constructor
  · intro h
    have hy := congrArg Prod.snd h
    change x.2 = y.2 at hy
    have hx := congrArg Prod.fst h
    change ramp x.1 + |x.2| * x.1 = ramp y.1 + |y.2| * y.1 at hx
    rw [← hy] at hx
    by_cases hz : x.2 = 0
    · rw [hz, abs_zero, zero_mul, zero_mul, add_zero, add_zero] at hx
      rcases ramp_equal x.1 y.1 hx with he | ⟨hxx, hyy⟩
      · exact Or.inl (Prod.ext he hy)
      · right
        constructor
        · exact ⟨⟨x.1, hxx⟩, Prod.ext rfl hz.symm⟩
        · exact ⟨⟨y.1, hyy⟩, Prod.ext rfl (hy.symm.trans hz).symm⟩
    · have hp : 0 < |x.2| := abs_pos.mpr hz
      have he : x.1 = y.1 := by
        rcases lt_trichotomy x.1 y.1 with hlt | he | hgt
        · have hm := ramp_mono hlt.le
          have hs := mul_lt_mul_of_pos_left hlt hp
          linarith
        · exact he
        · have hm := ramp_mono hgt.le
          have hs := mul_lt_mul_of_pos_left hgt hp
          linarith
      exact Or.inl (Prod.ext he hy)
  · rintro (rfl | ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩)
    · rfl
    · simp only [collapseSegment, abs_zero, zero_mul, add_zero,
        (ramp_zero s.val).mpr s.property, (ramp_zero t.val).mpr t.property]

theorem exists_arc_collapse (gamma : ArcParameter → Plane)
    (hc : Continuous gamma) (hi : Function.Injective gamma) :
    ∃ q : Plane → Plane, Continuous q ∧ ∀ x y,
      q x = q y ↔ x = y ∨ (x ∈ Set.range gamma ∧ y ∈ Set.range gamma) := by
  obtain ⟨c, hs⟩ := FiniteAvalanches.External.parametrized_plane_arc_straightening gamma hc hi
  refine ⟨collapseSegment ∘ c.map, collapseSegment_continuous.comp c.map.continuous, ?_⟩
  intro x y
  have hr (z : Plane) : c.map z ∈ Set.range (fun t : ArcParameter => (t.val, (0 : ℝ))) ↔
      z ∈ Set.range gamma := by
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, c.map.injective ((hs t).trans ht)⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, (hs t).symm⟩
  change collapseSegment (c.map x) = collapseSegment (c.map y) ↔ _
  rw [collapseSegment_equal, c.map.injective.eq_iff, hr, hr]

end FiniteAvalanches.Electrical.ArcCollapse
