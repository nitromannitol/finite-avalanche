import FiniteAvalanches.Electrical.Geometry.CellExterior
import FiniteAvalanches.Electrical.Geometry.PathContinua

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeCell
open LatticeProb
open scoped Classical
noncomputable section

theorem integer_vertex_exterior (a b : ℤ) :
    1 ≤ ((a : ℝ) + (b : ℝ) - 1)^2 + ((b : ℝ) - (a : ℝ))^2 := by
  by_cases h : a ≠ 0 ∨ (b ≠ 0 ∧ b ≠ 1)
  · simpa using horizontal_exterior a b 0 (by norm_num) (by norm_num) h
  · push Not at h
    have ha : a = 0 := h.1
    have hb : b = 0 ∨ b = 1 := by omega
    rcases hb with rfl | rfl <;> simp [ha]

theorem sitePoint_exterior (o p : Site 2) : cellMap o (sitePoint p) ∈ exterior := by
  have h := integer_vertex_exterior (p 0-o 0) (p 1-o 1)
  dsimp [exterior,cellMap,sitePoint]
  push_cast at h
  nlinarith [h]

theorem alternating_no_cell_side (D : Set (Site 2)) (o p : Site 2) (i : Fin 2)
    (hAlt : Alternating D o) (hp : p ∈ D) (hq : p + unit i ∈ D) : ¬CellSide o p i := by
  have e01 : corner o 0 + unit 0 = corner o 1 := by simp [corner]
  have e32 : corner o 3 + unit 0 = corner o 2 := by simp [corner]; abel
  have e03 : corner o 0 + unit 1 = corner o 3 := by simp [corner]
  have e12 : corner o 1 + unit 1 = corner o 2 := by simp [corner,add_assoc]
  intro hs
  rcases hAlt with ⟨h0,h2,h1,h3⟩ | ⟨h1,h3,h0,h2⟩
  · rcases hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact h1 (e01 ▸ hq)
    · exact h3 hp
    · exact h3 (e03 ▸ hq)
    · exact h1 hp
  · rcases hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact h0 hp
    · exact h2 (e32 ▸ hq)
    · exact h0 hp
    · exact h2 (e12 ▸ hq)

theorem alternating_compl (D : Set (Site 2)) (o : Site 2)
    (h : Alternating D o) : Alternating Dᶜ o := by
  rcases h with ⟨h0,h2,h1,h3⟩ | ⟨h1,h3,h0,h2⟩
  · exact Or.inr ⟨h1,h3,by simpa using h0,by simpa using h2⟩
  · exact Or.inl ⟨h0,h2,by simpa using h1,by simpa using h3⟩

theorem alternating_trace_exterior (D : Set (Site 2)) (o : Site 2) (h : Alternating D o) :
    cellMap o '' latticeTrace D ⊆ exterior := by
  rintro z ⟨w,hw,rfl⟩
  rcases hw with ⟨p,hp,rfl⟩ | ⟨p,i,hp,hq,t,ht,rfl⟩
  · exact sitePoint_exterior o p
  · exact unitSegment_outside_cell_circle o p i t ht (alternating_no_cell_side D o p i h hp hq)

/-- The actual alternating-cell obstruction, from literal induced nearest-neighbor connectedness.
No dual circuit, rotation, path-order, disk drawing, or lattice obstruction is supplied. -/
theorem not_alternating_of_connected (D : Set (Site 2))
    (hD : ((lattice 2).induce D).Connected) (hDc : ((lattice 2).induce Dᶜ).Connected)
    (o : Site 2) : ¬Alternating D o := by
  have impossible (A : Set (Site 2))
      (hA : ((lattice 2).induce A).Connected) (hAc : ((lattice 2).induce Aᶜ).Connected)
      (h0 : corner o 0 ∈ A) (h2 : corner o 2 ∈ A)
      (h1 : corner o 1 ∉ A) (h3 : corner o 3 ∉ A) : False := by
    have hAlt : Alternating A o := Or.inl ⟨h0,h2,h1,h3⟩
    obtain ⟨K,L,hKc,hKconn,hLc,hLconn,hKt,hLt,hKL,h0K,h2K,h1L,h3L⟩ :=
      opposite_paths_continua A (corner o 0) (corner o 2) (corner o 1) (corner o 3)
        hA hAc h0 h2 h1 h3
    have hc := cellMap_continuous o
    have hi : Disjoint (cellMap o '' K) (cellMap o '' L) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨x,hx,rfl⟩ ⟨y,hy,hxy⟩
      have he := cellMap_injective o hxy.symm
      exact Set.disjoint_left.mp hKL hx (he ▸ hy)
    have hKe : cellMap o '' K ⊆ exterior :=
      (Set.image_mono hKt).trans (alternating_trace_exterior A o hAlt)
    have hLe : cellMap o '' L ⊆ exterior :=
      (Set.image_mono hLt).trans (alternating_trace_exterior Aᶜ o (alternating_compl A o hAlt))
    apply exterior_alternation_impossible (cellMap o '' K) (cellMap o '' L)
      (hKc.image hc) (hKconn.image _ hc.continuousOn)
      (hLc.image hc) (hLconn.image _ hc.continuousOn) hKe hLe hi
    · simpa only [cellMap_sitePoint,(cellCoordinates_corner o).2.2.1] using
        Set.mem_image_of_mem (cellMap o) h2K
    · simpa only [cellMap_sitePoint,(cellCoordinates_corner o).1] using
        Set.mem_image_of_mem (cellMap o) h0K
    · simpa only [cellMap_sitePoint,(cellCoordinates_corner o).2.2.2] using
        Set.mem_image_of_mem (cellMap o) h3L
    · simpa only [cellMap_sitePoint,(cellCoordinates_corner o).2.1] using
        Set.mem_image_of_mem (cellMap o) h1L
  intro h
  rcases h with ⟨h0,h2,h1,h3⟩ | ⟨h1,h3,h0,h2⟩
  · exact impossible D hD hDc h0 h2 h1 h3
  · apply impossible Dᶜ hDc (by have he : Dᶜᶜ = D := compl_compl D; rw [he]; exact hD) h0 h2
    · simpa using h1
    · simpa using h3

/-- Every two D-corners of a unit cell are joined inside that cell in at most two steps. -/
theorem two_step_cell_path (D : Finset (Site 2))
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (o : Site 2) (i j : Fin 4) (hi : corner o i ∈ D) (hj : corner o j ∈ D) :
    NearWithin (↑D : Set (Site 2)) o (corner o i) (corner o j) := by
  rcases near_or_alternating (↑D : Set (Site 2)) o i j hi hj with h | h
  · exact h
  · exact (not_alternating_of_connected (↑D : Set (Site 2)) hD hDc o h).elim

end
end FiniteAvalanches.Electrical.LatticeCell
