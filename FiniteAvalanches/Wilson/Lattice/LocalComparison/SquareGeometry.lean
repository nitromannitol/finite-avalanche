import FiniteAvalanches.Wilson.Lattice.LocalComparison.SourceNetwork

set_option autoImplicit false
namespace LocalSquareGeometry
open LatticeProb FiniteAvalanches
open FiniteAvalanches.Electrical.Plane.SourceLattice
open scoped Classical
noncomputable section

def xy (x y : ℤ) : Site 2 := fun i => if i = 0 then x else y

/-- Clockwise traversal of the radius-j square, with its endpoint repeated. -/
def vertex (j t : ℕ) : Site 2 :=
  if (t : ℤ) ≤ 2*(j : ℤ) then xy ((j : ℤ)-t) j
  else if (t : ℤ) ≤ 4*(j : ℤ) then xy (-(j : ℤ)) (3*(j : ℤ)-t)
  else if (t : ℤ) ≤ 6*(j : ℤ) then xy ((t : ℤ)-5*j) (-(j : ℤ))
  else xy j ((t : ℤ)-7*j)

/-- The positive-coordinate ID of each physical square edge. -/
def edge (j t : ℕ) : OriginalCopy :=
  if (t : ℤ) < 2*(j : ℤ) then (xy ((j : ℤ)-t-1) j,0)
  else if (t : ℤ) < 4*(j : ℤ) then (xy (-(j : ℤ)) (3*(j : ℤ)-t-1),1)
  else if (t : ℤ) < 6*(j : ℤ) then (xy ((t : ℤ)-5*j) (-(j : ℤ)),0)
  else (xy j ((t : ℤ)-7*j),1)

theorem vertex_end (j : ℕ) : vertex j (8*j) = vertex j 0 := by
  ext i
  fin_cases i <;> simp only [vertex] <;> split_ifs <;> simp [xy] <;> omega

theorem vertex_radius (j t : ℕ) (ht : t ≤ 8*j) : siteRadius 0 (vertex j t) = j := by
  have hc := JointMetricGeometry.radius_cast (vertex j t)
  apply Int.ofNat_inj.mp
  rw [hc]
  simp only [Needle.radius,vertex]
  split_ifs <;> simp [xy,abs_eq_max_neg]
  all_goals omega

theorem edge_endpoints (j t : ℕ) (ht : t < 8*j) :
    (originalA (edge j t) = vertex j t ∧ originalB (edge j t) = vertex j (t+1)) ∨
    (originalA (edge j t) = vertex j (t+1) ∧ originalB (edge j t) = vertex j t) := by
  by_cases h0 : (t : ℤ) < 2*(j : ℤ)
  · right
    constructor <;> ext i <;> fin_cases i <;>
      simp only [edge,if_pos h0,originalA,originalB,vertex,Pi.add_apply]
    all_goals split_ifs <;> simp [xy,unit] <;> omega
  · by_cases h1 : (t : ℤ) < 4*(j : ℤ)
    · right
      constructor <;> ext i <;> fin_cases i <;>
        simp only [edge,if_neg h0,if_pos h1,originalA,originalB,vertex,Pi.add_apply]
      all_goals split_ifs <;> simp [xy,unit] <;> omega
    · by_cases h2 : (t : ℤ) < 6*(j : ℤ)
      · left
        constructor <;> ext i <;> fin_cases i <;>
          simp only [edge,if_neg h0,if_neg h1,if_pos h2,originalA,originalB,vertex,Pi.add_apply]
        all_goals split_ifs <;> simp [xy,unit] <;> omega
      · left
        constructor <;> ext i <;> fin_cases i <;>
          simp only [edge,if_neg h0,if_neg h1,if_neg h2,originalA,originalB,vertex,Pi.add_apply]
        all_goals split_ifs <;> simp [xy,unit] <;> omega

theorem edge_radius (j t : ℕ) (ht : t < 8*j) :
    siteRadius 0 (originalA (edge j t)) = j ∧ siteRadius 0 (originalB (edge j t)) = j := by
  have hstart := vertex_radius j t ht.le
  have hend := vertex_radius j (t+1) (by omega)
  rcases edge_endpoints j t ht with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact ⟨ha ▸ hstart,hb ▸ hend⟩
  · exact ⟨ha ▸ hend,hb ▸ hstart⟩

theorem edge_injective (j : ℕ) (hj : 0 < j) :
    Function.Injective (fun t : Fin (8*j) => edge j t.val) := by
  intro s t he
  have hs := s.isLt
  have ht := t.isLt
  have hd := congrArg Prod.snd he
  have hx := congrArg (fun e : OriginalCopy => e.1 0) he
  have hy := congrArg (fun e : OriginalCopy => e.1 1) he
  apply Fin.ext
  dsimp [edge] at hd hx hy
  split_ifs at hd hx hy <;> simp_all [xy]

def copies (j : ℕ) : Finset OriginalCopy :=
  Finset.univ.image (fun t : Fin (8*j) => edge j t.val)

theorem copies_card (j : ℕ) (hj : 0 < j) : (copies j).card = 8*j := by
  rw [copies,Finset.card_image_of_injective _ (edge_injective j hj),Finset.card_univ,Fintype.card_fin]

theorem copies_disjoint (j k : ℕ) (hjk : j ≠ k) : Disjoint (copies j) (copies k) := by
  apply Finset.disjoint_left.mpr
  intro e hej hek
  obtain ⟨s,_,hs⟩ := Finset.mem_image.mp hej
  obtain ⟨t,_,ht⟩ := Finset.mem_image.mp hek
  have hrj := (edge_radius j s.val s.isLt).1
  have hrk := (edge_radius k t.val t.isLt).1
  rw [hs] at hrj
  rw [ht] at hrk
  exact hjk (hrj.symm.trans hrk)

/-- The source marked edge meets zero, whereas every square edge has both
endpoints at a positive radius. -/
theorem source_mark_not_mem (j : ℕ) (hj : 0 < j) (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (b : Site 2)
    (hm : (originalA marked.val = 0 ∧ originalB marked.val = b) ∨
      (originalA marked.val = b ∧ originalB marked.val = 0)) : marked.val ∉ copies j := by
  intro h
  obtain ⟨t,_,ht⟩ := Finset.mem_image.mp h
  have hr := edge_radius j t.val t.isLt
  rw [ht] at hr
  rcases hm with ⟨ha,_⟩ | ⟨_,hb⟩
  · rw [ha] at hr
    have hz : siteRadius (0 : Site 2) 0 = 0 := by simp [siteRadius]
    rw [hz] at hr
    omega
  · rw [hb] at hr
    have hz : siteRadius (0 : Site 2) 0 = 0 := by simp [siteRadius]
    rw [hz] at hr
    omega

/-- Every vertex on the actual square has an index in this traversal. -/
theorem vertex_surjective (j : ℕ) (hj : 0 < j) (x : Site 2) (hx : siteRadius 0 x = j) :
    ∃ t : Fin (8*j), vertex j t.val = x := by
  have hr := JointMetricGeometry.radius_cast x
  rw [hx] at hr
  simp only [Needle.radius,abs_eq_max_neg] at hr
  have hb : -(j : ℤ) ≤ x 0 ∧ x 0 ≤ j ∧ -(j : ℤ) ≤ x 1 ∧ x 1 ≤ j := by omega
  have he : x 0 = j ∨ x 0 = -(j : ℤ) ∨ x 1 = j ∨ x 1 = -(j : ℤ) := by omega
  by_cases htop : x 1 = j
  · let t := ((j : ℤ)-x 0).toNat
    have ht : (t : ℤ) = (j : ℤ)-x 0 := Int.toNat_of_nonneg (by omega)
    have htlt : t < 8*j := by omega
    refine ⟨⟨t,htlt⟩,?_⟩
    ext i
    fin_cases i <;> simp only [vertex] <;> split_ifs <;> simp [xy] <;> omega
  · by_cases hleft : x 0 = -(j : ℤ)
    · let t := (3*(j : ℤ)-x 1).toNat
      have ht : (t : ℤ) = 3*(j : ℤ)-x 1 := Int.toNat_of_nonneg (by omega)
      have htlt : t < 8*j := by omega
      refine ⟨⟨t,htlt⟩,?_⟩
      ext i
      fin_cases i <;> simp only [vertex] <;> split_ifs <;> simp [xy] <;> omega
    · by_cases hbottom : x 1 = -(j : ℤ)
      · let t := (5*(j : ℤ)+x 0).toNat
        have ht : (t : ℤ) = 5*(j : ℤ)+x 0 := Int.toNat_of_nonneg (by omega)
        have htlt : t < 8*j := by omega
        refine ⟨⟨t,htlt⟩,?_⟩
        ext i
        fin_cases i <;> simp only [vertex] <;> split_ifs <;> simp [xy] <;> omega
      · have hright : x 0 = j := by omega
        let t := (7*(j : ℤ)+x 1).toNat
        have ht : (t : ℤ) = 7*(j : ℤ)+x 1 := Int.toNat_of_nonneg (by omega)
        have htlt : t < 8*j := by omega
        refine ⟨⟨t,htlt⟩,?_⟩
        ext i
        fin_cases i <;> simp only [vertex] <;> split_ifs <;> simp [xy] <;> omega

end
end LocalSquareGeometry
