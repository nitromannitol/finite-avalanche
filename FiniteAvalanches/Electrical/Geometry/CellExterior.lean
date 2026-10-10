import FiniteAvalanches.Electrical.Geometry.ExteriorAlternation
import FiniteAvalanches.Electrical.Geometry.UnitSegments

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeCell
open LatticeProb
open scoped Classical
noncomputable section

def cellMap (o : Site 2) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 + z.2 - ((o 0 : ℝ) + (o 1 : ℝ) + 1),
   z.2 - z.1 - ((o 1 : ℝ) - (o 0 : ℝ)))

theorem cellMap_continuous (o : Site 2) : Continuous (cellMap o) := by
  unfold cellMap
  fun_prop

theorem cellMap_injective (o : Site 2) : Function.Injective (cellMap o) := by
  intro x y h
  have h0 := congrArg Prod.fst h
  have h1 := congrArg Prod.snd h
  dsimp [cellMap] at h0 h1
  apply Prod.ext <;> linarith

theorem cellMap_sitePoint (o p : Site 2) : cellMap o (sitePoint p) = cellCoordinates o p := rfl

def CellSide (o p : Site 2) (i : Fin 2) : Prop :=
  (p = corner o 0 ∧ i = 0) ∨ (p = corner o 3 ∧ i = 0) ∨
  (p = corner o 0 ∧ i = 1) ∨ (p = corner o 1 ∧ i = 1)

/-- Pure scalar geometry of every horizontal integer unit segment except the two cell sides. -/
theorem horizontal_exterior (a b : ℤ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hab : a ≠ 0 ∨ (b ≠ 0 ∧ b ≠ 1)) :
    1 ≤ ((a : ℝ) + (b : ℝ) + t - 1)^2 + ((b : ℝ) - (a : ℝ) - t)^2 := by
  by_cases hb0 : b = 0
  · subst b
    have ha : a ≠ 0 := hab.elim id (fun h => (h.1 rfl).elim)
    have ha' : a ≤ -1 ∨ 1 ≤ a := by omega
    rcases ha' with ha' | ha'
    · have har : (a : ℝ) ≤ -1 := by exact_mod_cast ha'
      norm_num
      nlinarith [sq_nonneg ((a : ℝ) + t)]
    · have har : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha'
      norm_num
      nlinarith [sq_nonneg ((a : ℝ) + t - 1)]
  by_cases hb1 : b = 1
  · subst b
    have ha : a ≠ 0 := hab.elim id (fun h => (h.2 rfl).elim)
    have ha' : a ≤ -1 ∨ 1 ≤ a := by omega
    rcases ha' with ha' | ha'
    · have har : (a : ℝ) ≤ -1 := by exact_mod_cast ha'
      norm_num
      nlinarith [sq_nonneg ((a : ℝ) + t)]
    · have har : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha'
      norm_num
      nlinarith [sq_nonneg ((a : ℝ) + t - 1)]
  have hb : b ≤ -1 ∨ 2 ≤ b := by omega
  rcases hb with hb | hb
  · have hbr : (b : ℝ) ≤ -1 := by exact_mod_cast hb
    nlinarith [sq_nonneg ((a : ℝ) + t - 1/2),sq_nonneg ((b : ℝ) + 1)]
  · have hbr : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    nlinarith [sq_nonneg ((a : ℝ) + t - 1/2),sq_nonneg ((b : ℝ) - 2)]

theorem site_ext {p q : Site 2} (h0 : p 0 = q 0) (h1 : p 1 = q 1) : p = q := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

theorem unitSegment_outside_cell_circle (o p : Site 2) (i : Fin 2) (t : ℝ)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hside : ¬CellSide o p i) :
    cellMap o (unitSegment p i t) ∈ exterior := by
  fin_cases i
  · have hab : p 0 - o 0 ≠ 0 ∨ (p 1 - o 1 ≠ 0 ∧ p 1 - o 1 ≠ 1) := by
      by_contra h
      push Not at h
      have hp0 : p 0 = o 0 := by omega
      have hp : p 1 - o 1 = 0 ∨ p 1 - o 1 = 1 := by omega
      rcases hp with hp1 | hp1
      · have he : p = corner o 0 := site_ext (by simpa [corner] using hp0)
          (by simp [corner]; omega)
        exact hside (Or.inl ⟨he,rfl⟩)
      · have he : p = corner o 3 := site_ext (by simpa [corner,unit] using hp0)
          (by simp [corner,unit]; omega)
        exact hside (Or.inr (Or.inl ⟨he,rfl⟩))
    have h := horizontal_exterior (p 0-o 0) (p 1-o 1) t ht.1 ht.2 hab
    dsimp [exterior,cellMap,unitSegment]
    simp only [unit,Pi.single_apply,Fin.ext_iff]
    norm_num
    push_cast at h
    nlinarith [h]
  · have hab : p 1 - o 1 ≠ 0 ∨ (p 0 - o 0 ≠ 0 ∧ p 0 - o 0 ≠ 1) := by
      by_contra h
      push Not at h
      have hp1 : p 1 = o 1 := by omega
      have hp : p 0 - o 0 = 0 ∨ p 0 - o 0 = 1 := by omega
      rcases hp with hp0 | hp0
      · have he : p = corner o 0 := site_ext (by simp [corner]; omega)
          (by simpa [corner] using hp1)
        exact hside (Or.inr (Or.inr (Or.inl ⟨he,rfl⟩)))
      · have he : p = corner o 1 := site_ext (by simp [corner,unit]; omega)
          (by simpa [corner,unit] using hp1)
        exact hside (Or.inr (Or.inr (Or.inr ⟨he,rfl⟩)))
    have h := horizontal_exterior (p 1-o 1) (p 0-o 0) t ht.1 ht.2 hab
    dsimp [exterior,cellMap,unitSegment]
    simp only [unit,Pi.single_apply,Fin.ext_iff]
    norm_num
    push_cast at h
    nlinarith [h]

end
end FiniteAvalanches.Electrical.LatticeCell
