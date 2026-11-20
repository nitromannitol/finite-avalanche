import FiniteAvalanches.Wilson.Lattice.WiredDualFaceGraph

/-! Vertex and edge counts for the wired square and its dual face square. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- The wired square has one contracted sink in addition to its active vertices. -/
theorem card_wiredVertices (B : ℕ) :
    Fintype.card (FiniteWired.Vertex B) = (2 * B + 1)^2 + 1 := by
  simp only [FiniteWired.Vertex, Fintype.card_option, FiniteWired.Active, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_Icc, Int.card_Icc]
  have h : (Int.toNat ((B : ℤ) + 1 - (-(B : ℤ)))) = 2 * B + 1 := by omega
  rw [h]

/-- The dual face square has an even number of vertices along each side. -/
theorem card_wiredDualFaces (B : ℕ) :
    Fintype.card (WiredDualFace B) = (2 * B + 2)^2 := by
  simp only [WiredDualFace, Fintype.card_fun, Fintype.card_fin, Fintype.card_Icc, Int.card_Icc]
  congr 1
  omega

/-- The possible coordinate along a positively oriented face-square edge. -/
abbrev DualFaceLongCoordinate (B : ℕ) := Set.Icc (-(B : ℤ) - 1) ((B : ℤ) - 1)

/-- The possible coordinate transverse to a face-square edge. -/
abbrev DualFaceTransverseCoordinate (B : ℕ) := Set.Icc (-(B : ℤ) - 1) (B : ℤ)

/-- Positively oriented lattice edges with both endpoints in the dual face square. -/
abbrev DualFaceBaseEdges (B : ℕ) :=
  {p : Site 2 × Fin 2 // inDualFaceBox B p.1 ∧ inDualFaceBox B (p.1 + unit p.2)}

/-- Choose one coordinate along a direction and the other transverse to it. -/
def dualFaceBaseSite (i : Fin 2) (a b : ℤ) : Site 2 := fun j => if j = i then a else b

/-- Direction, longitudinal coordinate, and transverse coordinate determine an
oriented edge of the dual face square. -/
def dualFaceBaseOfCoordinates (B : ℕ)
    (p : Fin 2 × DualFaceLongCoordinate B × DualFaceTransverseCoordinate B) : DualFaceBaseEdges B :=
  ⟨(dualFaceBaseSite p.1 p.2.1.val p.2.2.val, p.1), by
    rcases p with ⟨i, a, b⟩
    have ha := a.property
    have hb := b.property
    change -(B : ℤ) - 1 ≤ a.val ∧ a.val ≤ (B : ℤ) - 1 at ha
    change -(B : ℤ) - 1 ≤ b.val ∧ b.val ≤ (B : ℤ) at hb
    fin_cases i <;>
      simp only [inDualFaceBox, Fin.forall_fin_two, dualFaceBaseSite, Pi.add_apply, unit,
        Pi.single_apply] <;> norm_num at * <;> omega⟩

/-- Recover the direction and two coordinates of an oriented face-square edge. -/
def dualFaceBaseCoordinates (B : ℕ) (p : DualFaceBaseEdges B) :
    Fin 2 × DualFaceLongCoordinate B × DualFaceTransverseCoordinate B :=
  (p.val.2, ⟨p.val.1 p.val.2, by
      have h := p.property.1 p.val.2
      have hn := p.property.2 p.val.2
      have hn' : -(B : ℤ) - 1 ≤ p.val.1 p.val.2 + 1 ∧ p.val.1 p.val.2 + 1 ≤ B := by
        simpa [unit] using hn
      change -(B : ℤ) - 1 ≤ p.val.1 p.val.2 ∧ p.val.1 p.val.2 ≤ (B : ℤ) - 1
      omega⟩,
    ⟨p.val.1 (1 - p.val.2), p.property.1 (1 - p.val.2)⟩)

/-- Oriented face-square edges are exactly their direction and two coordinates. -/
def dualFaceBaseCoordinatesEquiv (B : ℕ) :
    (Fin 2 × DualFaceLongCoordinate B × DualFaceTransverseCoordinate B) ≃ DualFaceBaseEdges B where
  toFun := dualFaceBaseOfCoordinates B
  invFun := dualFaceBaseCoordinates B
  left_inv p := by
    rcases p with ⟨i, a, b⟩
    fin_cases i <;> simp [dualFaceBaseCoordinates, dualFaceBaseOfCoordinates, dualFaceBaseSite]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · funext j
      have h := p.property
      rcases p with ⟨⟨z, i⟩, hp⟩
      fin_cases i <;> fin_cases j <;> simp [dualFaceBaseCoordinates, dualFaceBaseOfCoordinates, dualFaceBaseSite]
    · rfl

/-- Every oriented face-square edge determines its original lattice edge. -/
def dualFaceBaseEdgeEquiv (B : ℕ) :
    DualFaceBaseEdges B ≃ {e : LatticeEdge // ∀ z ∈ e.val, inDualFaceBox B z} where
  toFun p := ⟨baseEdge p.val, by
    intro z hz
    have hz' : z = p.val.1 ∨ z = p.val.1 + unit p.val.2 := by
      simpa only [baseEdge, Sym2.mem_iff] using hz
    rcases hz' with rfl | rfl
    · exact p.property.1
    · exact p.property.2⟩
  invFun e := ⟨edgeEquiv.symm e.val, by
    have h : baseEdge (edgeEquiv.symm e.val) = e.val := edgeEquiv.apply_symm_apply e.val
    constructor
    · apply e.property
      have hs : (edgeEquiv.symm e.val).1 ∈ (baseEdge (edgeEquiv.symm e.val)).val := by
        simp [baseEdge]
      exact (congrArg (fun z : LatticeEdge => (edgeEquiv.symm e.val).1 ∈ z.val) h).mp hs
    · apply e.property
      have hs : (edgeEquiv.symm e.val).1 + unit (edgeEquiv.symm e.val).2 ∈
          (baseEdge (edgeEquiv.symm e.val)).val := by
        simp [baseEdge]
      exact (congrArg (fun z : LatticeEdge =>
        (edgeEquiv.symm e.val).1 + unit (edgeEquiv.symm e.val).2 ∈ z.val) h).mp hs⟩
  left_inv p := by
    apply Subtype.ext
    exact edgeEquiv.symm_apply_apply p.val
  right_inv e := by
    apply Subtype.ext
    exact edgeEquiv.apply_symm_apply e.val

/-- Wired edge copies correspond to direction and two face-square coordinates. -/
def wiredCopyFaceCoordinatesEquiv (B : ℕ) :
    FiniteWired.Edge B ≃ Fin 2 × DualFaceLongCoordinate B × DualFaceTransverseCoordinate B :=
  (wiredCopyDualFaceEdgeEquiv B).trans ((dualFaceBaseEdgeEquiv B).symm.trans
    (dualFaceBaseCoordinatesEquiv B).symm)

/-- The exact number of wired copies, including the separate exits. -/
theorem card_wiredEdgeCopies (B : ℕ) :
    Fintype.card (FiniteWired.Edge B) = 2 * (2 * B + 1) * (2 * B + 2) := by
  rw [Fintype.card_congr (wiredCopyFaceCoordinatesEquiv B)]
  simp only [Fintype.card_prod, Fintype.card_fin, DualFaceLongCoordinate,
    DualFaceTransverseCoordinate, Fintype.card_Icc, Int.card_Icc]
  have h1 : (Int.toNat ((B : ℤ) - 1 + 1 - (-(B : ℤ) - 1))) = 2 * B + 1 := by omega
  have h2 : (Int.toNat ((B : ℤ) + 1 - (-(B : ℤ) - 1))) = 2 * B + 2 := by omega
  rw [h1, h2]
  ring

/-- The wired box and its face square satisfy the finite Euler count. -/
theorem wiredDualFace_euler_count (B : ℕ) :
    Fintype.card (FiniteWired.Edge B) + 2 =
      Fintype.card (FiniteWired.Vertex B) + Fintype.card (WiredDualFace B) := by
  rw [card_wiredEdgeCopies, card_wiredVertices, card_wiredDualFaces]
  ring

end
end FiniteAvalanches.Wilson.Lattice
