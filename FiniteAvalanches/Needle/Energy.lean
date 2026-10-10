import FiniteAvalanches.Needle.Geometry

open FiniteAvalanches.Sandpile.FiniteWired

namespace FiniteAvalanches.Needle
open LatticeProb
open scoped BigOperators Classical

private theorem min_ratio_ordered (a b d e : ℝ)
    (ha : 0 ≤ a) (hd : 0 < d) (he : 0 < e)
    (hab : b ≤ a+1) (hde : d ≤ e+1) :
    min 1 (b/e) - min 1 (a/d) ≤ 2/e := by
  by_cases hua : 1 ≤ a/d
  · rw [min_eq_left hua]
    have hmin : min 1 (b/e) ≤ 1 := min_le_left _ _
    have hp : 0 ≤ 2/e := by positivity
    linarith only [hmin, hp]
  · have had : a ≤ d := by
      have := (div_lt_iff₀ hd).mp (lt_of_not_ge hua)
      linarith only [this]
    rw [min_eq_right (le_of_not_ge hua)]
    have hh : a*(d-e) ≤ d := by
      have hh := mul_le_mul_of_nonneg_left (show d-e ≤ 1 by linarith only [hde]) ha
      nlinarith only [hh, had]
    have hr : (a+1)/e-a/d ≤ 2/e := by
      apply (le_div_iff₀ he).mpr
      have hd0 := hd.ne'
      field_simp
      nlinarith only [hh]
    have hrb : b/e ≤ (a+1)/e := (div_le_div_iff_of_pos_right he).mpr hab
    exact (sub_le_sub_right ((min_le_right _ _).trans hrb) _).trans hr

theorem min_ratio_lipschitz (a b d e s : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 < s)
    (hd : s ≤ d) (he : s ≤ e)
    (hab : a ≤ b+1) (hba : b ≤ a+1)
    (hde : d ≤ e+1) (hed : e ≤ d+1) :
    |min 1 (a/d)-min 1 (b/e)| ≤ 2/s := by
  have hdpos := hs.trans_le hd
  have hepos := hs.trans_le he
  have h1 := min_ratio_ordered a b d e ha hdpos hepos hba hde
  have h2 := min_ratio_ordered b a e d hb hepos hdpos hab hed
  have hdv : 2/d ≤ 2/s := div_le_div_of_nonneg_left (by norm_num) hs hd
  have hev : 2/e ≤ 2/s := div_le_div_of_nonneg_left (by norm_num) hs he
  rw [abs_le]
  constructor <;> linarith only [h1, h2, hdv, hev]

/-- The distance-ratio potential, with the wired exterior at value one. -/
noncomputable def trial (h L : ℕ) (p : Fin (L+1) → Point) : Vertex (2*h) → ℝ
  | none => 1
  | some x => min 1 ((targetDistance (target h L p) (target_nonempty h L p) (site x) : ℝ) /
      (depth (2*h) x : ℝ))

theorem trial_bounds (h L : ℕ) (p : Fin (L+1) → Point) (v : Vertex (2*h)) :
    0 ≤ trial h L p v ∧ trial h L p v ≤ 1 := by
  cases v with
  | none => norm_num [trial]
  | some x => exact ⟨le_min (by norm_num) (by positivity), min_le_left _ _⟩

theorem trial_zero (h L : ℕ) (p : Fin (L+1) → Point) (x : Active (2*h))
    (hx : site x ∈ target h L p) : trial h L p (some x) = 0 := by
  rw [trial, (targetDistance_zero_iff _ _ _).mpr hx]
  norm_num

theorem trial_neighbor (h L : ℕ) (p : Fin (L+1) → Point) (x y : Active (2*h))
    (hxy : (lattice 2).Adj (site x) (site y)) :
    |trial h L p (some x)-trial h L p (some y)| ≤
      2/(min (depth (2*h) x) (depth (2*h) y) : ℝ) := by
  have hs : 0 < (min (depth (2*h) x) (depth (2*h) y) : ℝ) := by
    exact_mod_cast lt_min (depth_pos _ _) (depth_pos _ _)
  apply min_ratio_lipschitz _ _ _ _ _ (by positivity) (by positivity) hs
  · exact_mod_cast min_le_left _ _
  · exact_mod_cast min_le_right _ _
  · exact_mod_cast targetDistance_neighbor _ _ hxy
  · exact_mod_cast targetDistance_neighbor _ _ hxy.symm
  · exact_mod_cast depth_neighbor _ _ _ hxy
  · exact_mod_cast depth_neighbor _ _ _ hxy.symm

theorem trial_eq_one_of_far (h L : ℕ) (p : Fin (L+1) → Point) (x : Active (2*h))
    (hx : depth (2*h) x ≤ targetDistance (target h L p) (target_nonempty h L p) (site x)) :
    trial h L p (some x) = 1 := by
  apply min_eq_left
  apply (le_div_iff₀ (by exact_mod_cast depth_pos (2*h) x)).mpr
  simpa only [one_mul] using (Nat.cast_le.mpr hx : (depth (2*h) x : ℝ) ≤ _)

theorem active_endpoint_near (h L : ℕ) (p : Fin (L+1) → Point) (x y : Active (2*h))
    (hxy : (lattice 2).Adj (site x) (site y))
    (hd : depth (2*h) x ≤ depth (2*h) y)
    (hne : trial h L p (some x) ≠ trial h L p (some y)) :
    targetDistance (target h L p) (target_nonempty h L p) (site x) ≤ depth (2*h) x+2 := by
  by_contra hx
  have hy := targetDistance_neighbor (target h L p) (target_nonempty h L p) hxy
  have hdy := depth_neighbor (2*h) y x hxy.symm
  have hex := trial_eq_one_of_far h L p x (by omega)
  have hey := trial_eq_one_of_far h L p y (by omega)
  exact hne (hex.trans hey.symm)


theorem axis_dist_le (x : Point) (d : Direction) (k : ℕ) :
    (lattice 2).dist x (x+(k:ℤ) • step d) ≤ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hadj (q : Point) : (lattice 2).Adj q (q+step d) := by
      rcases d with ⟨i, b⟩
      cases b
      · exact Graph.Zd.adj_iff.mpr ⟨i, Or.inr (by simp [step, sub_eq_add_neg])⟩
      · exact Graph.Zd.adj_iff.mpr ⟨i, Or.inl (by simp [step])⟩
    have he : x+((k+1:ℕ):ℤ) • step d = (x+(k:ℤ) • step d)+step d := by
      push_cast; module
    rw [he]
    have ht := (Graph.Zd.latticeConnected 2).dist_triangle
      (u:=x) (v:=x+(k:ℤ) • step d) (w:=(x+(k:ℤ) • step d)+step d)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr (hadj _)] at ht
    omega

theorem depth_le_dist_exterior (N : ℕ) (x : Active N) (y : Point) (hy : y ∉ box 2 N) :
    depth N x ≤ (lattice 2).dist (site x) y := by
  have hr : (N:ℤ) < radius y := by
    rw [mem_box_iff] at hy
    omega
  have ht := radius_le_dist_add y (site x)
  rw [SimpleGraph.dist_comm] at ht
  have hd := depth_cast N x
  omega

theorem exists_exterior_at_depth (N : ℕ) (x : Active N) :
    ∃ y ∉ box 2 N, (lattice 2).dist (site x) y = depth N x := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, |site x i| = radius (site x) := by
    by_cases hh : |site x 0| ≤ |site x 1|
    · exact ⟨1, (max_eq_right hh).symm⟩
    · exact ⟨0, (max_eq_left (le_of_not_ge hh)).symm⟩
  let d : Direction := (i, decide (0 ≤ site x i))
  let y := site x + (depth N x : ℤ) • step d
  have hd := depth_cast N x
  have hy : y ∉ box 2 N := by
    intro hbox
    have hbi := hbox i
    dsimp [y, d, step] at hbi
    by_cases hx : 0 ≤ site x i
    · simp [hx, unit] at hbi
      rw [abs_of_nonneg hx] at hi
      have hh := (abs_le.mp hbi).2
      omega
    · simp [hx, unit] at hbi
      rw [abs_of_neg (lt_of_not_ge hx)] at hi
      have hh := (abs_le.mp hbi).1
      omega
  exact ⟨y, hy, le_antisymm (axis_dist_le _ _ _) (depth_le_dist_exterior N x y hy)⟩

/-- Distance to the literal complementary lattice set, on its interior carrier. -/
noncomputable def exteriorDistance (N : ℕ) (x : Active N) : ℕ :=
  sInf {n | ∃ y ∉ box 2 N, (lattice 2).dist (site x) y = n}

theorem exteriorDistance_eq_depth (N : ℕ) (x : Active N) :
    exteriorDistance N x = depth N x := by
  obtain ⟨y, hy, hd⟩ := exists_exterior_at_depth N x
  apply le_antisymm
  · exact Nat.sInf_le ⟨y, hy, hd⟩
  · apply le_csInf (show ({n | ∃ y ∉ box 2 N, (lattice 2).dist (site x) y = n} : Set ℕ).Nonempty from ⟨depth N x, y, hy, hd⟩)
    rintro n ⟨z, hz, he⟩
    rw [← he]
    exact depth_le_dist_exterior N x z hz


/-- Assign each original copy to an incidence of minimum interior depth. -/
noncomputable def charge (N : ℕ) : Edge N → Active N × Direction
  | .inl e =>
      if depth N e.val.1 ≤ depth N e.val.2 then
        (e.val.1, (e.property.choose, true))
      else (e.val.2, (e.property.choose, false))
  | .inr e => e.val

theorem directionEdge_interior_left (N : ℕ) (e : InteriorEdge N) :
    directionEdge e.val.1 (e.property.choose, true) = .inl e := by
  have he := e.property.choose_spec
  have hin : inBox N (site e.val.1+unit e.property.choose) := by
    rw [← he]; exact fun i => (e.val.2 i).property
  simp only [directionEdge, dif_pos hin]
  congr 1
  apply Subtype.ext
  change (e.val.1, activeOfSite N (site e.val.1+unit e.property.choose) hin) = e.val
  apply Prod.ext
  · rfl
  · apply site_injective N
    exact he.symm

theorem directionEdge_interior_right (N : ℕ) (e : InteriorEdge N) :
    directionEdge e.val.2 (e.property.choose, false) = .inl e := by
  have he := e.property.choose_spec
  have hin : inBox N (site e.val.2-unit e.property.choose) := by
    have he' : site e.val.2-unit e.property.choose = site e.val.1 := by
      calc
        _ = (site e.val.1+unit e.property.choose)-unit e.property.choose :=
          congrArg (fun q => q-unit e.property.choose) he
        _ = _ := add_sub_cancel_right _ _
    rw [he']; exact fun i => (e.val.1 i).property
  simp only [directionEdge, dif_pos hin]
  congr 1
  apply Subtype.ext
  change (activeOfSite N (site e.val.2-unit e.property.choose) hin, e.val.2) = e.val
  apply Prod.ext
  · apply site_injective N
    change site e.val.2-unit e.property.choose = site e.val.1
    calc
      _ = (site e.val.1+unit e.property.choose)-unit e.property.choose :=
        congrArg (fun q => q-unit e.property.choose) he
      _ = _ := add_sub_cancel_right _ _
  · rfl

theorem directionEdge_charge (N : ℕ) (e : Edge N) :
    directionEdge (charge N e).1 (charge N e).2 = e := by
  cases e with
  | inl e =>
    dsimp [charge]
    split
    · exact directionEdge_interior_left N e
    · exact directionEdge_interior_right N e
  | inr e => exact direction_edge_exit e.val.1 e.val.2 e.property

theorem charge_injective (N : ℕ) : Function.Injective (charge N) := by
  intro e f h
  have hh := congrArg (fun q : Active N × Direction => directionEdge q.1 q.2) h
  simpa only [directionEdge_charge] using hh

theorem step_adj (x : Point) (d : Direction) : (lattice 2).Adj x (x+step d) := by
  rcases d with ⟨i, b⟩
  cases b
  · exact Graph.Zd.adj_iff.mpr ⟨i, Or.inr (by simp [step, sub_eq_add_neg])⟩
  · exact Graph.Zd.adj_iff.mpr ⟨i, Or.inl (by simp [step])⟩

theorem exit_depth (N : ℕ) (e : ExitEdge N) : depth N e.val.1 = 1 := by
  have hle := depth_le_dist_exterior N e.val.1 (site e.val.1+step e.val.2)
    (by exact fun hx => e.property ((inBox_iff N _).mpr hx))
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr (step_adj _ _)] at hle
  have hp := depth_pos N e.val.1
  omega

noncomputable def vertexWeight (h L : ℕ) (p : Fin (L+1) → Point) (x : Active (2*h)) : ℝ :=
  if targetDistance (target h L p) (target_nonempty h L p) (site x) ≤ depth (2*h) x+2
  then (2/(depth (2*h) x : ℝ))^2 else 0

theorem vertexWeight_nonneg (h L : ℕ) (p : Fin (L+1) → Point) (x : Active (2*h)) :
    0 ≤ vertexWeight h L p x := by unfold vertexWeight; split <;> positivity

theorem edge_trial_le_weight (h L : ℕ) (p : Fin (L+1) → Point) (e : Edge (2*h)) :
    (trial h L p (endpoints e).1-trial h L p (endpoints e).2)^2 ≤
      vertexWeight h L p (charge (2*h) e).1 := by
  cases e with
  | inl e =>
    have hadj : (lattice 2).Adj (site e.val.1) (site e.val.2) :=
      ⟨e.property.choose, Or.inl e.property.choose_spec⟩
    have hsq (x y : Active (2*h)) (hxy : (lattice 2).Adj (site x) (site y))
        (hd : depth (2*h) x ≤ depth (2*h) y) :
        (trial h L p (some x)-trial h L p (some y))^2 ≤ vertexWeight h L p x := by
      by_cases heq : trial h L p (some x) = trial h L p (some y)
      · rw [heq, sub_self, zero_pow (by decide)]
        exact vertexWeight_nonneg h L p x
      · have hn := active_endpoint_near h L p x y hxy hd heq
        rw [vertexWeight, if_pos hn]
        have hb := trial_neighbor h L p x y hxy
        rw [min_eq_left (Nat.cast_le.mpr hd)] at hb
        have hc : 0 ≤ 2/(depth (2*h) x:ℝ) := by positivity
        nlinarith only [sq_abs (trial h L p (some x)-trial h L p (some y)),
          mul_nonneg (abs_nonneg (trial h L p (some x)-trial h L p (some y)))
            (sub_nonneg.mpr hb), mul_nonneg hc (sub_nonneg.mpr hb)]
    dsimp [charge, endpoints]
    split
    · rename_i hd
      exact hsq _ _ hadj hd
    · rename_i hd
      have hh := hsq _ _ hadj.symm (le_of_not_ge hd)
      simpa only [sub_sq_comm] using hh
  | inr e =>
    have hd := exit_depth (2*h) e
    by_cases hn : targetDistance (target h L p) (target_nonempty h L p) (site e.val.1) ≤
        depth (2*h) e.val.1+2
    · dsimp [endpoints, charge]
      rw [vertexWeight, if_pos hn, hd]
      obtain ⟨h0, h1⟩ := trial_bounds h L p (some e.val.1)
      have hb : (trial h L p (some e.val.1)-1)^2 ≤ (4:ℝ) := by
        nlinarith only [h0, h1, mul_nonneg h0 (sub_nonneg.mpr h1)]
      simpa only [trial, Nat.cast_one, div_one, show (2:ℝ)^2 = 4 by norm_num] using hb
    · have hf := trial_eq_one_of_far h L p e.val.1 (by omega)
      dsimp [endpoints, charge]
      rw [vertexWeight, if_neg hn, hf]
      norm_num [trial]

/-- Once-counted original-copy energy is charged injectively to four incidences per vertex. -/
theorem trial_energy_le_vertex_sum (h L : ℕ) (p : Fin (L+1) → Point) :
    FiniteAvalanches.Electrical.energy (fun e : Edge (2*h) => (endpoints e).1)
      (fun e => (endpoints e).2) (trial h L p) ≤ 4 * ∑ x, vertexWeight h L p x := by
  unfold FiniteAvalanches.Electrical.energy
  calc
    _ ≤ ∑ e : Edge (2*h), vertexWeight h L p (charge (2*h) e).1 :=
      Finset.sum_le_sum (fun e _ => edge_trial_le_weight h L p e)
    _ = ∑ q ∈ Finset.univ.image (charge (2*h)), vertexWeight h L p q.1 :=
      (Finset.sum_image (f:=fun q : Active (2*h) × Direction => vertexWeight h L p q.1)
        (fun _ _ _ _ he => charge_injective (2*h) he)).symm
    _ ≤ ∑ q : Active (2*h) × Direction, vertexWeight h L p q.1 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun q _ _ => vertexWeight_nonneg h L p q.1)
    _ = 4 * ∑ x, vertexWeight h L p x := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, Direction, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_bool, Nat.reduceMul, nsmul_eq_mul]
      rw [Finset.mul_sum]
      norm_num only [Nat.cast_ofNat]

/-- The finite sum is decomposed by actual positive exterior-distance layers. -/
theorem vertex_sum_eq_layers (h L : ℕ) (p : Fin (L+1) → Point) :
    (∑ x, vertexWeight h L p x) =
      ∑ s ∈ Finset.Icc 1 (2*h+1), ((nearLayer h L s p).card : ℝ) * (2/(s:ℝ))^2 := by
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s:=Finset.univ) (t:=Finset.Icc 1 (2*h+1)) (g:=depth (2*h))
    (fun x _ => Finset.mem_Icc.mpr ⟨depth_pos _ _, depth_le _ _⟩)
    (vertexWeight h L p)
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro s hs
  have hset : nearLayer h L s p =
      (Finset.univ.filter (fun x => depth (2*h) x = s)).filter
        (fun x => targetDistance (target h L p) (target_nonempty h L p) (site x) ≤ s+2) := by
    ext x; simp [nearLayer]
  rw [hset, ← Finset.sum_boole, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  have hd := (Finset.mem_filter.mp hx).2
  simp only [vertexWeight, hd, ite_mul, one_mul, zero_mul]

/-- The new paper-specific energy estimate; every layer-count premise is produced above. -/
theorem trial_energy_le_harmonic (h L : ℕ) (p : Fin (L+1) → Point) (z : Point)
    (hp : ∀ t, linf z (p t) ≤ 2*h-radius (p t)+1) :
    FiniteAvalanches.Electrical.energy (fun e : Edge (2*h) => (endpoints e).1)
      (fun e => (endpoints e).2) (trial h L p) ≤
        960 * ∑ s ∈ Finset.Icc 1 (2*h+1), 1/(s:ℝ) := by
  apply (trial_energy_le_vertex_sum h L p).trans
  rw [vertex_sum_eq_layers]
  calc
    _ ≤ 4 * ∑ s ∈ Finset.Icc 1 (2*h+1), (60*s:ℝ)*(2/(s:ℝ))^2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro s hs
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact_mod_cast card_nearLayer h L s p z (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2 hp
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      have hs0 : (s:ℝ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by have := (Finset.mem_Icc.mp hs).1; omega)
      field_simp
      ring


end FiniteAvalanches.Needle
