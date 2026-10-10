module

public import FiniteAvalanches.Electrical.Geometry.Charging

/-! Geometric consumption of current squares and finite ordered boundary intervals. -/

@[expose] public section

namespace FiniteAvalanches.Electrical.Geometry

open scoped BigOperators Classical

theorem Square.side_le_min_of_subset (Q : Square) (M : ℝ)
    (hQ : Q.carrier ⊆ rectangle 0 1 0 M) : Q.side ≤ min 1 M := by
  have hcorner : (Q.x,Q.y) ∈ Q.carrier :=
    ⟨⟨le_rfl,by linarith [Q.side_nonneg]⟩,⟨le_rfl,by linarith [Q.side_nonneg]⟩⟩
  have hend : (Q.x+Q.side,Q.y+Q.side) ∈ Q.carrier :=
    ⟨⟨by linarith [Q.side_nonneg],le_rfl⟩,⟨by linarith [Q.side_nonneg],le_rfl⟩⟩
  have ha := hQ hcorner
  have hb := hQ hend
  exact le_min (by linarith [ha.1.1,hb.1.2]) (by linarith [ha.2.1,hb.2.2])

theorem angular_axis_eq_zero (epsilon y0 y : ℝ) (he : 0 < epsilon)
    (hy : y ≤ y0-epsilon) : angular epsilon y0 (0,y) = 0 := by
  have hn : y-y0 < 0 := by linarith
  have hd : epsilon ≤ |y-y0| := by rw [abs_of_neg hn]; linarith
  change 1/2+(y-y0)/(2*max epsilon (max |(0:ℝ)| |y-y0|)) = 0
  rw [abs_zero, max_eq_right (abs_nonneg (y-y0)), max_eq_right hd, abs_of_neg hn]
  field_simp [ne_of_lt hn]
  ring

theorem angular_axis_eq_one (epsilon y0 y : ℝ) (he : 0 < epsilon)
    (hy : y0+epsilon ≤ y) : angular epsilon y0 (0,y) = 1 := by
  have hn : 0 < y-y0 := by linarith
  have hd : epsilon ≤ |y-y0| := by rw [abs_of_pos hn]; linarith
  change 1/2+(y-y0)/(2*max epsilon (max |(0:ℝ)| |y-y0|)) = 1
  rw [abs_zero, max_eq_right (abs_nonneg (y-y0)), max_eq_right hd, abs_of_pos hn]
  field_simp
  ring

/-- Actual finite cumulative stream heights; parallel boundary copies remain separate indices. -/
noncomputable def boundaryHeight {m : ℕ} (s : Fin m → ℝ) (i : ℕ) : ℝ :=
  ∑ j : Fin m, if j.val < i then s j else 0

theorem boundaryHeight_mono {m : ℕ} (s : Fin m → ℝ) (hs : ∀ i, 0 ≤ s i) :
    Monotone (boundaryHeight s) := by
  intro i j hij
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k.val < i
  · simp [hk, Nat.lt_of_lt_of_le hk hij]
  · simp only [if_neg hk]
    split <;> simp_all

theorem boundaryHeight_succ {m : ℕ} (s : Fin m → ℝ) (i : Fin m) :
    boundaryHeight s (i.val+1) = boundaryHeight s i.val+s i := by
  have h : ∀ j : Fin m, (if j.val < i.val+1 then s j else 0) =
      (if j.val < i.val then s j else 0) + (if j = i then s j else 0) := by
    intro j
    by_cases hji : j = i
    · subst j; simp
    · have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
      by_cases hlt : j.val < i.val
      · simp [hji, hlt, Nat.lt_succ_of_lt hlt]
      · have hlt' : ¬ j.val < i.val+1 := by omega
        simp [hji,hlt,hlt']
  simp only [boundaryHeight,h,Finset.sum_add_distrib]
  simp

/-- Midpoints on the lower side stay at least half the adjacent current below the split. -/
theorem boundary_midpoint_le {m : ℕ} (s : Fin m → ℝ) (hs : ∀ i, 0 ≤ s i)
    (i j : Fin m) (hij : i.val ≤ j.val) :
    boundaryHeight s i.val+s i/2 ≤ boundaryHeight s (j.val+1)-s j/2 := by
  have hj := boundaryHeight_succ s j
  by_cases heq : i = j
  · subst i; linarith only [hj]
  · have hnext : i.val+1 ≤ j.val := by have hn : i.val ≠ j.val := fun h => heq (Fin.ext h); omega
    have hmono := boundaryHeight_mono s hs hnext
    have hi := boundaryHeight_succ s i
    linarith only [hj,hi,hmono,hs i,hs j]

/-- The corresponding bound above the split. -/
theorem boundary_midpoint_ge {m : ℕ} (s : Fin m → ℝ) (hs : ∀ i, 0 ≤ s i)
    (i j : Fin m) (hij : j.val ≤ i.val) :
    boundaryHeight s j.val+s j/2 ≤ boundaryHeight s i.val+s i/2 := by
  by_cases heq : i = j
  · subst i; exact le_rfl
  · have hnext : j.val+1 ≤ i.val := by have hn : i.val ≠ j.val := fun h => heq (Fin.ext h); omega
    have hmono := boundaryHeight_mono s hs hnext
    have hj := boundaryHeight_succ s j
    linarith only [hj,hmono,hs i,hs j]

/-- No exceptional alpha edge is needed when the common comparison height is its midpoint. -/
theorem boundary_axis_midpoint {m : ℕ} (s : Fin m → ℝ) (hs : ∀ i, 0 ≤ s i)
    (j0 j1 : Fin m) (hj : j0.val+1 = j1.val) (epsilon : ℝ) (he : 0 < epsilon)
    (he0 : 2*epsilon ≤ s j0) (he1 : 2*epsilon ≤ s j1) (i : Fin m) :
    angular epsilon (boundaryHeight s j1.val) (0,boundaryHeight s i.val+s i/2) =
      if i.val < j1.val then 0 else 1 := by
  split
  · rename_i hi
    apply angular_axis_eq_zero _ _ _ he
    have h := boundary_midpoint_le s hs i j0 (by omega)
    rw [hj] at h
    linarith only [h,he0]
  · rename_i hi
    apply angular_axis_eq_one _ _ _ he
    have h := boundary_midpoint_ge s hs i j1 (by omega)
    linarith only [h,he1]

/-- Literal segment containment derived from its range bound and an incident maximal square. -/
theorem segment_subset_dilate (Q : Square) (d lo hi x : ℝ) (hd : 1 ≤ d)
    (hx : x = Q.x ∨ x = Q.x+Q.side)
    (hlo : lo ≤ Q.y) (hhi : Q.y+Q.side ≤ hi) (hlen : hi-lo ≤ d*Q.side) :
    {z : ℝ × ℝ | z.1 = x ∧ lo ≤ z.2 ∧ z.2 ≤ hi} ⊆
      (Q.dilate (2*d+3) (by linarith)).carrier := by
  intro z hz
  have hn := Q.side_nonneg
  have hdn : 0 ≤ d*Q.side := mul_nonneg (by linarith) hn
  dsimp [Square.carrier, Square.dilate]
  rcases hx with rfl | rfl
  · exact ⟨⟨by linarith [hz.1],by linarith [hz.1]⟩,
      ⟨by linarith [hz.2.1],by linarith [hz.2.2]⟩⟩
  · exact ⟨⟨by linarith [hz.1],by linarith [hz.1]⟩,
      ⟨by linarith [hz.2.1],by linarith [hz.2.2]⟩⟩

/-- Closed square sides, including shared boundaries, are valid comparison points. -/
theorem Square.carrier_subset_dilate (Q : Square) (lambda : ℝ) (hl : 1 ≤ lambda) :
    Q.carrier ⊆ (Q.dilate lambda (by linarith)).carrier := by
  intro z hz
  have h := mul_nonneg (by linarith : 0 ≤ lambda-1) Q.side_nonneg
  dsimp [Square.carrier,Square.dilate]
  exact ⟨⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩,
    ⟨by linarith [hz.2.1],by linarith [hz.2.2]⟩⟩

/-- Zero-current point squares have exactly zero oscillation even after dilation. -/
theorem Square.angularOsc_eq_zero_of_side_eq_zero (Q : Square) (epsilon y0 lambda : ℝ)
    (he : 0 < epsilon) (hl : 1 ≤ lambda) (hs : Q.side = 0) :
    Q.angularOsc epsilon y0 lambda hl he = 0 := by
  have h := Q.angularOsc_bounds epsilon y0 lambda he hl
  rw [hs,mul_zero,zero_div] at h
  exact le_antisymm h.2.2 h.1

end FiniteAvalanches.Electrical.Geometry
