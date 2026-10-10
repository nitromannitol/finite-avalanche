import FiniteAvalanches.Electrical.Geometry.CellCases

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeCell
open LatticeProb
open scoped Classical
noncomputable section

/-- The literal straight drawing of the original positive unit copy (p,i). -/
def unitSegment (p : Site 2) (i : Fin 2) (t : ℝ) : ℝ × ℝ :=
  ((p 0 : ℝ) + t * (unit i 0 : ℝ), (p 1 : ℝ) + t * (unit i 1 : ℝ))
def sitePoint (p : Site 2) : ℝ × ℝ := ((p 0 : ℝ),(p 1 : ℝ))

theorem sitePoint_injective : Function.Injective sitePoint := by
  intro p q h
  apply funext
  intro i
  fin_cases i
  · have hf := congrArg Prod.fst h
    dsimp [sitePoint] at hf
    exact_mod_cast hf
  · have hf := congrArg Prod.snd h
    dsimp [sitePoint] at hf
    exact_mod_cast hf

/-- Integer unit-edge rectangles can overlap only at a shared endpoint. -/
theorem integer_rectangle_shared (p q : Site 2) (i j : Fin 2)
    (h0 : p 0 ≤ q 0 + unit j 0) (h1 : q 0 ≤ p 0 + unit i 0)
    (h2 : p 1 ≤ q 1 + unit j 1) (h3 : q 1 ≤ p 1 + unit i 1) :
    p = q ∨ p = q + unit j ∨ p + unit i = q ∨ p + unit i = q + unit j := by
  fin_cases i <;> fin_cases j
  all_goals simp only [funext_iff,Fin.forall_fin_two,Pi.add_apply,unit,Pi.single_apply,Fin.ext_iff] at h0 h1 h2 h3 ⊢
  all_goals norm_num at h0 h1 h2 h3 ⊢
  all_goals omega

/-- A lattice vertex in the closed rectangle of a unit copy is one of its two endpoints. -/
theorem integer_rectangle_vertex (p q : Site 2) (j : Fin 2)
    (h0 : q 0 ≤ p 0) (h1 : p 0 ≤ q 0 + unit j 0)
    (h2 : q 1 ≤ p 1) (h3 : p 1 ≤ q 1 + unit j 1) :
    p = q ∨ p = q + unit j := by
  fin_cases j
  all_goals simp only [funext_iff,Fin.forall_fin_two,Pi.add_apply,unit,Pi.single_apply,Fin.ext_iff] at h0 h1 h2 h3 ⊢
  all_goals norm_num at h0 h1 h2 h3 ⊢
  all_goals omega

theorem unit_coord_nonneg (i j : Fin 2) : (0 : ℝ) ≤ (unit i j : ℤ) := by
  fin_cases i <;> fin_cases j <;> norm_num [unit]

theorem unitSegment_bounds (p : Site 2) (i : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (p 0 : ℝ) ≤ (unitSegment p i t).1 ∧
    (unitSegment p i t).1 ≤ (p 0 : ℝ) + (unit i 0 : ℝ) ∧
    (p 1 : ℝ) ≤ (unitSegment p i t).2 ∧
    (unitSegment p i t).2 ≤ (p 1 : ℝ) + (unit i 1 : ℝ) := by
  have h0 := unit_coord_nonneg i 0
  have h1 := unit_coord_nonneg i 1
  dsimp [unitSegment]
  constructor
  · nlinarith [mul_nonneg ht.1 h0]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right ht.2 h0]
  constructor
  · nlinarith [mul_nonneg ht.1 h1]
  · nlinarith [mul_le_mul_of_nonneg_right ht.2 h1]

theorem unitSegment_intersection_shared (p q : Site 2) (i j : Fin 2) (s t : ℝ)
    (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (h : unitSegment p i s = unitSegment q j t) :
    p = q ∨ p = q + unit j ∨ p + unit i = q ∨ p + unit i = q + unit j := by
  obtain ⟨hp0,hp1,hp2,hp3⟩ := unitSegment_bounds p i s hs
  obtain ⟨hq0,hq1,hq2,hq3⟩ := unitSegment_bounds q j t ht
  rw [h] at hp0 hp1 hp2 hp3
  apply integer_rectangle_shared p q i j
  · exact_mod_cast hp0.trans hq1
  · exact_mod_cast hq0.trans hp1
  · exact_mod_cast hp2.trans hq3
  · exact_mod_cast hq2.trans hp3

theorem sitePoint_mem_unitSegment (p q : Site 2) (j : Fin 2) (t : ℝ)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (h : sitePoint p = unitSegment q j t) :
    p = q ∨ p = q + unit j := by
  obtain ⟨h0,h1,h2,h3⟩ := unitSegment_bounds q j t ht
  rw [← h] at h0 h1 h2 h3
  dsimp [sitePoint] at h0 h1 h2 h3
  apply integer_rectangle_vertex p q j
  · exact_mod_cast h0
  · exact_mod_cast h1
  · exact_mod_cast h2
  · exact_mod_cast h3

/-- The literal union of D vertices and all original positive unit copies with endpoints in D. -/
def latticeTrace (D : Set (Site 2)) : Set (ℝ × ℝ) :=
  (sitePoint '' D) ∪ {z | ∃ p i, p ∈ D ∧ p + unit i ∈ D ∧
    ∃ t ∈ Set.Icc (0:ℝ) 1, unitSegment p i t = z}

theorem latticeTrace_disjoint {D A : Set (Site 2)} (hDA : Disjoint D A) :
    Disjoint (latticeTrace D) (latticeTrace A) := by
  apply Set.disjoint_left.mpr
  intro z hzD hzA
  rcases hzD with ⟨p,hp,rfl⟩ | ⟨p,i,hp,hpi,s,hs,hps⟩
  · rcases hzA with ⟨q,hq,hqp⟩ | ⟨q,j,hq,hqj,t,ht,hqt⟩
    · exact Set.disjoint_left.mp hDA hp (sitePoint_injective hqp ▸ hq)
    · rcases sitePoint_mem_unitSegment p q j t ht hqt.symm with h | h
      · exact Set.disjoint_left.mp hDA hp (h.symm ▸ hq)
      · exact Set.disjoint_left.mp hDA hp (h.symm ▸ hqj)
  · rcases hzA with ⟨q,hq,hqz⟩ | ⟨q,j,hq,hqj,t,ht,hqt⟩
    · rcases sitePoint_mem_unitSegment q p i s hs (hqz.trans hps.symm) with h | h
      · exact Set.disjoint_left.mp hDA hp (h ▸ hq)
      · exact Set.disjoint_left.mp hDA hpi (h ▸ hq)
    · rcases unitSegment_intersection_shared p q i j s t hs ht (hps.trans hqt.symm) with h | h | h | h
      · exact Set.disjoint_left.mp hDA hp (h.symm ▸ hq)
      · exact Set.disjoint_left.mp hDA hp (h.symm ▸ hqj)
      · exact Set.disjoint_left.mp hDA hpi (h.symm ▸ hq)
      · exact Set.disjoint_left.mp hDA hpi (h.symm ▸ hqj)

end
end FiniteAvalanches.Electrical.LatticeCell
