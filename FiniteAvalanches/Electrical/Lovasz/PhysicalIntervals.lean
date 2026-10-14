import FiniteAvalanches.Electrical.Lovasz.PathSlices

/-! Consecutive closed and open stream intervals in either physical cut-path
orientation. Reversing orientation preserves the actual interval carriers. -/

namespace FiniteAvalanches.Electrical.Lovasz
open scoped Classical

/-- An increasing or decreasing path covers its closed endpoint interval. -/
theorem fin_path_unordered_interval_cover (m : ℕ) (hm : 0 < m)
    (H : Fin (m + 1) → ℝ)
    (hstep : (∀ i : Fin m, H i.castSucc < H i.succ) ∨
      (∀ i : Fin m, H i.succ < H i.castSucc))
    (u : ℝ) (hu : u ∈ Set.Icc (min (H 0) (H (Fin.last m))) (max (H 0) (H (Fin.last m)))) :
    ∃ i : Fin m, u ∈ Set.Icc (min (H i.castSucc) (H i.succ)) (max (H i.castSucc) (H i.succ)) := by
  rcases hstep with hstep | hstep
  · have hmono : StrictMono H := Fin.strictMono_iff_lt_succ.mpr hstep
    have hend : H 0 ≤ H (Fin.last m) := hmono.monotone (Fin.zero_le _)
    rw [min_eq_left hend, max_eq_right hend] at hu
    obtain ⟨i, hi⟩ := fin_path_interval_cover m hm H hstep u hu.1 hu.2
    exact ⟨i, by simpa only [Set.mem_Icc, min_eq_left (hstep i).le, max_eq_right (hstep i).le] using hi⟩
  · have hanti : StrictAnti H := Fin.strictAnti_iff_succ_lt.mpr hstep
    have hend : H (Fin.last m) ≤ H 0 := hanti.antitone (Fin.zero_le _)
    rw [min_eq_right hend, max_eq_left hend] at hu
    obtain ⟨i, hi⟩ := fin_path_interval_cover m hm (fun k => -H k)
      (fun i => neg_lt_neg (hstep i)) (-u) (neg_le_neg hu.2) (neg_le_neg hu.1)
    refine ⟨i, ?_⟩
    rw [min_eq_right (hstep i).le, max_eq_left (hstep i).le]
    exact ⟨neg_le_neg_iff.mp hi.2, neg_le_neg_iff.mp hi.1⟩

/-- Every vertex value lies between the endpoints of either monotone orientation. -/
theorem fin_path_vertex_bounds (m : ℕ) (H : Fin (m + 1) → ℝ)
    (hstep : (∀ i : Fin m, H i.castSucc < H i.succ) ∨
      (∀ i : Fin m, H i.succ < H i.castSucc)) (k : Fin (m + 1)) :
    min (H 0) (H (Fin.last m)) ≤ H k ∧ H k ≤ max (H 0) (H (Fin.last m)) := by
  rcases hstep with hstep | hstep
  · have hm : Monotone H := (Fin.strictMono_iff_lt_succ.mpr hstep).monotone
    exact ⟨(min_le_left _ _).trans (hm (Fin.zero_le k)),
      (hm (Fin.le_last k)).trans (le_max_right _ _)⟩
  · have hm : Antitone H := (Fin.strictAnti_iff_succ_lt.mpr hstep).antitone
    exact ⟨(min_le_right _ _).trans (hm (Fin.le_last k)),
      (hm (Fin.zero_le k)).trans (le_max_left _ _)⟩

/-- Distinct consecutive intervals of a monotone physical path have disjoint interiors. -/
theorem fin_path_unordered_interval_disjoint (m : ℕ) (H : Fin (m + 1) → ℝ)
    (hstep : (∀ i : Fin m, H i.castSucc < H i.succ) ∨
      (∀ i : Fin m, H i.succ < H i.castSucc))
    (i j : Fin m) (hij : i ≠ j) :
    Disjoint
      (Set.Ioo (min (H i.castSucc) (H i.succ)) (max (H i.castSucc) (H i.succ)))
      (Set.Ioo (min (H j.castSucc) (H j.succ)) (max (H j.castSucc) (H j.succ))) := by
  rcases hstep with hstep | hstep
  · rw [min_eq_left (hstep i).le, max_eq_right (hstep i).le,
      min_eq_left (hstep j).le, max_eq_right (hstep j).le]
    exact fin_path_interval_disjoint m H hstep i j hij
  · have hd := fin_path_interval_disjoint m (fun k => -H k)
      (fun i => neg_lt_neg (hstep i)) i j hij
    rw [min_eq_right (hstep i).le, max_eq_left (hstep i).le,
      min_eq_right (hstep j).le, max_eq_left (hstep j).le]
    apply Set.disjoint_left.mpr
    intro u hi hj
    exact Set.disjoint_left.mp hd
      ⟨neg_lt_neg hi.2, neg_lt_neg hi.1⟩ ⟨neg_lt_neg hj.2, neg_lt_neg hj.1⟩

end FiniteAvalanches.Electrical.Lovasz

#print axioms FiniteAvalanches.Electrical.Lovasz.fin_path_unordered_interval_cover
#print axioms FiniteAvalanches.Electrical.Lovasz.fin_path_unordered_interval_disjoint
#print axioms FiniteAvalanches.Electrical.Lovasz.fin_path_vertex_bounds
