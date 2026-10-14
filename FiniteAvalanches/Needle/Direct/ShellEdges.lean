import FiniteAvalanches.Needle.Sharp.Edges

/-! Counting copied lattice edges by their farther endpoint. -/

namespace FiniteAvalanches.Needle
open LatticeProb Sandpile.FiniteWired
open scoped Classical

/-- The vertices at a fixed positive maximum-norm distance from a center. -/
noncomputable def needleShell (w : Point) (k : ℕ) : Finset Point :=
  ((Finset.Ioo (-(k : ℤ)) k).image (fun t => ![w 0 + k, w 1 + t])) ∪
  ((Finset.Ioo (-(k : ℤ)) k).image (fun t => ![w 0 - k, w 1 + t])) ∪
  ((Finset.Icc (-(k : ℤ)) k).image (fun t => ![w 0 + t, w 1 + k])) ∪
  ((Finset.Icc (-(k : ℤ)) k).image (fun t => ![w 0 + t, w 1 - k]))

theorem mem_needleShell (w x : Point) (k : ℕ) (hx : linf x w = k) :
    x ∈ needleShell w k := by
  have h0 := (radius_le_iff (x - w) (k : ℤ)).mp hx.le 0
  have h1 := (radius_le_iff (x - w) (k : ℤ)).mp hx.le 1
  have hside : |x 0 - w 0| = k ∨ |x 1 - w 1| = k := by
    exact (max_eq_iff.mp hx).imp And.left And.left
  by_cases hy : |x 1 - w 1| = k
  · have hsign : x 1 - w 1 = k ∨ x 1 - w 1 = -(k : ℤ) := by
      rw [abs_eq_max_neg] at hy
      omega
    rcases hsign with ht | hb
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨x 0 - w 0, Finset.mem_Icc.mpr (abs_le.mp h0), ?_⟩
      funext i
      fin_cases i <;> dsimp <;> omega
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨x 0 - w 0, Finset.mem_Icc.mpr (abs_le.mp h0), ?_⟩
      funext i
      fin_cases i <;> dsimp <;> omega
  · have hv := hside.resolve_right hy
    have ht : x 1 - w 1 ∈ Finset.Ioo (-(k : ℤ)) k := by
      simp only [Pi.sub_apply] at h1
      apply Finset.mem_Ioo.mpr
      rw [abs_eq_max_neg] at h1 hy
      omega
    have hsign : x 0 - w 0 = k ∨ x 0 - w 0 = -(k : ℤ) := by
      rw [abs_eq_max_neg] at hv
      omega
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    rcases hsign with hr | hl
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨x 1 - w 1, ht, ?_⟩
      funext i
      fin_cases i <;> dsimp <;> omega
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨x 1 - w 1, ht, ?_⟩
      funext i
      fin_cases i <;> dsimp <;> omega

/-- Two complete horizontal sides and two corner-free vertical sides use eight k vertices. -/
theorem card_needleShell_le (w : Point) (k : ℕ) (hk : 1 ≤ k) :
    (needleShell w k).card ≤ 8 * k := by
  have hc : (Finset.Icc (-(k : ℤ)) k).card = 2 * k + 1 := by
    rw [Int.card_Icc]
    omega
  have ho : (Finset.Ioo (-(k : ℤ)) k).card = 2 * k - 1 := by
    rw [Int.card_Ioo]
    omega
  have hR := Finset.card_image_le (s := Finset.Ioo (-(k : ℤ)) k)
    (f := fun t => (![w 0 + k, w 1 + t] : Point))
  have hL := Finset.card_image_le (s := Finset.Ioo (-(k : ℤ)) k)
    (f := fun t => (![w 0 - k, w 1 + t] : Point))
  have hT := Finset.card_image_le (s := Finset.Icc (-(k : ℤ)) k)
    (f := fun t => (![w 0 + t, w 1 + k] : Point))
  have hB := Finset.card_image_le (s := Finset.Icc (-(k : ℤ)) k)
    (f := fun t => (![w 0 + t, w 1 - k] : Point))
  rw [hc] at hT hB
  rw [ho] at hR hL
  have h1 := Finset.card_union_le
    ((Finset.Ioo (-(k : ℤ)) k).image (fun t => (![w 0 + k, w 1 + t] : Point)))
    ((Finset.Ioo (-(k : ℤ)) k).image (fun t => (![w 0 - k, w 1 + t] : Point)))
  have h2 := Finset.card_union_le
    (((Finset.Ioo (-(k : ℤ)) k).image (fun t => (![w 0 + k, w 1 + t] : Point))) ∪
      ((Finset.Ioo (-(k : ℤ)) k).image (fun t => (![w 0 - k, w 1 + t] : Point))))
    ((Finset.Icc (-(k : ℤ)) k).image (fun t => (![w 0 + t, w 1 + k] : Point)))
  have h3 := Finset.card_union_le
    ((((Finset.Ioo (-(k : ℤ)) k).image (fun t => (![w 0 + k, w 1 + t] : Point))) ∪
      ((Finset.Ioo (-(k : ℤ)) k).image (fun t => (![w 0 - k, w 1 + t] : Point)))) ∪
      ((Finset.Icc (-(k : ℤ)) k).image (fun t => (![w 0 + t, w 1 + k] : Point))))
    ((Finset.Icc (-(k : ℤ)) k).image (fun t => (![w 0 + t, w 1 - k] : Point)))
  dsimp only [needleShell]
  omega

/-- Select the farther endpoint of the positive-coordinate geometric edge. -/
noncomputable def needleRadialCharge (w : Point) (q : Point × Fin 2) : Point × Direction :=
  if linf q.1 w ≤ linf (q.1 + unit q.2) w then
    (q.1 + unit q.2, (q.2, false)) else (q.1, (q.2, true))

private def positiveEdgeOfCharge (q : Point × Direction) : Point × Fin 2 :=
  (if q.2.2 then q.1 else q.1 - unit q.2.1, q.2.1)

private theorem positiveEdgeOfCharge_radial (w : Point) (q : Point × Fin 2) :
    positiveEdgeOfCharge (needleRadialCharge w q) = q := by
  unfold needleRadialCharge
  split <;> simp only [positiveEdgeOfCharge, Bool.false_eq_true, if_false,
    if_true, add_sub_cancel_right, Prod.eta]

theorem needleRadialCharge_injective (w : Point) :
    Function.Injective (needleRadialCharge w) :=
  Function.LeftInverse.injective (positiveEdgeOfCharge_radial w)

theorem needleRadialCharge_radius (w : Point) (q : Point × Fin 2) :
    linf (needleRadialCharge w q).1 w = max (linf q.1 w) (linf (q.1 + unit q.2) w) := by
  unfold needleRadialCharge
  split
  · rename_i hle
    exact (max_eq_right hle).symm
  · rename_i hle
    exact (max_eq_left (le_of_not_ge hle)).symm

/-- Each original wired copy is assigned to an endpoint and one of its four incidences. -/
noncomputable def needleEdgeCharge (N : ℕ) (w : Point) (e : Edge N) : Point × Direction :=
  needleRadialCharge w (Needle107Edges.key N e)

theorem needleEdgeCharge_injective (N : ℕ) (w : Point) :
    Function.Injective (needleEdgeCharge N w) :=
  (needleRadialCharge_injective w).comp (Needle107Edges.key_injective N)

/-- No more than thirty-two k original copies have maximum endpoint distance k. -/
theorem card_needle_edge_shell_le (N : ℕ) (w : Point) (k : ℕ) (hk : 1 ≤ k) :
    (Finset.univ.filter (fun e : Edge N => linf (needleEdgeCharge N w e).1 w = k)).card ≤
      32 * k := by
  let S := Finset.univ.filter (fun e : Edge N => linf (needleEdgeCharge N w e).1 w = k)
  have hsub : S.image (needleEdgeCharge N w) ⊆ needleShell w k ×ˢ Finset.univ := by
    intro q hq
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_product.mpr
      ⟨mem_needleShell w _ k (Finset.mem_filter.mp he).2, Finset.mem_univ _⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (needleEdgeCharge_injective N w),
    Finset.card_product, Finset.card_univ] at hc
  have hd : Fintype.card Direction = 4 := by
    simp only [Direction, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  rw [hd] at hc
  have hs := Nat.mul_le_mul_right 4 (card_needleShell_le w k hk)
  exact hc.trans (hs.trans (by omega))

end FiniteAvalanches.Needle
