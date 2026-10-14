import FiniteAvalanches.Electrical.Reference.CurrentRegularVertexCut
import FiniteAvalanches.Electrical.Geometry.CurrentFourCopyBondFaces

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.Plane.SourceLattice.CurrentRegularPhysical
open LatticeProb
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST
open CurrentRegularCut
open FiniteAvalanches.Electrical.BSST.CurrentBondFaces
open FiniteAvalanches.Electrical.BSST.CurrentChartFaces
open scoped Classical
noncomputable section

/-- The literal retained copied graph, without an extra rotation or face structure. -/
abbrev sourceGraph (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P) :
    CopiedGraph (Vertex D P) (Copy D P marked) := ⟨copyA D P marked,copyB D P marked⟩

variable (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)

/-- The closing arc has only the two actual terminal endpoints. -/
theorem closing_arc_not_regular (x : {x : D // x ∉ P.val}) :
    (augmentedGraph (sourceGraph D P marked) (alpha D P) (beta D P)).left (.inr ()) ≠ .inr x ∧
    (augmentedGraph (sourceGraph D P marked) (alpha D P) (beta D P)).right (.inr ()) ≠ .inr x := by
  simp [augmentedGraph,alpha,beta]

/-- Each cut ID at a regular site remains an original copy after closing the terminals. -/
theorem augmented_regular_star (x : {x : D // x ∉ P.val}) :
    (Finset.univ.filter fun e : Copy D P marked ⊕ Unit =>
      (augmentedGraph (sourceGraph D P marked) (alpha D P) (beta D P)).left e = .inr x ∨
      (augmentedGraph (sourceGraph D P marked) (alpha D P) (beta D P)).right e = .inr x) =
    (regularStar D P marked x).image Sum.inl := by
  classical
  ext e
  cases e with
  | inl e => simp [augmentedGraph,regularStar]
  | inr e => cases e; simp [augmentedGraph,alpha,beta]

theorem augmented_regular_star_card (x : {x : D // x ∉ P.val}) :
    (Finset.univ.filter fun e : Copy D P marked ⊕ Unit =>
      (augmentedGraph (sourceGraph D P marked) (alpha D P) (beta D P)).left e = .inr x ∨
      (augmentedGraph (sourceGraph D P marked) (alpha D P) (beta D P)).right e = .inr x).card = 4 := by
  classical
  rw [augmented_regular_star,Finset.card_image_of_injective _ Sum.inl_injective,regularStar_card]

/-- Actual copied walks avoiding the regular vertex survive unchanged in the closing-arc graph. -/
theorem augmented_reaches_without_regular (x : {x : D // x ∉ P.val})
    (u v : Vertex D P) (hu : u ≠ .inr x) (hv : v ≠ .inr x) :
    (augmentedGraph (sourceGraph D P marked) (alpha D P) (beta D P)).reaches
      (Finset.univ.filter fun e =>
        (augmentedGraph (sourceGraph D P marked) (alpha D P) (beta D P)).left e ≠ .inr x ∧
        (augmentedGraph (sourceGraph D P marked) (alpha D P) (beta D P)).right e ≠ .inr x) u v := by
  have hr := reaches_without_regular D P marked x u v hu hv
  induction hr with
  | refl => exact .refl
  | @tail v w _ hadj ih =>
    obtain ⟨e,he,hor⟩ := hadj
    have he' := (Finset.mem_filter.mp he).2
    have hv' : v ≠ .inr x := hor.elim (fun h => h.1 ▸ he'.1) (fun h => h.1 ▸ he'.2)
    exact (ih hv').tail ⟨.inl e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he'⟩,hor⟩

/-- The physical graph's singleton-complement connectivity is derived from the two-cut proof. -/
theorem source_without_regular_connected (x : {x : D // x ∉ P.val}) :
    ((supportGraph (copyA D P marked) (copyB D P marked)).induce
      {v : Vertex D P | v ≠ .inr x}).Connected := by
  have ha : alpha D P ≠ Sum.inr x := by simp [alpha]
  letI : Nonempty ↥({v : Vertex D P | v ≠ .inr x} : Set (Vertex D P)) := ⟨⟨alpha D P,ha⟩⟩
  refine ⟨?_⟩
  intro u v
  have hr := reaches_without_regular D P marked x u.val v.val u.property v.property
  have lift (a b : Vertex D P)
      (h : (StatementTypes.graph D P marked).reaches (withoutRegular D P marked x) a b)
      (ha : a ≠ .inr x) (hb : b ≠ .inr x) :
      ((supportGraph (copyA D P marked) (copyB D P marked)).induce
        {v : Vertex D P | v ≠ .inr x}).Reachable ⟨a,ha⟩ ⟨b,hb⟩ := by
    induction h with
    | refl => exact .rfl
    | @tail b c _ hadj ih =>
      obtain ⟨e,he,hor⟩ := hadj
      have he' := (Finset.mem_filter.mp he).2
      have hb' : b ≠ .inr x := hor.elim (fun h => h.1 ▸ he'.1) (fun h => h.1 ▸ he'.2)
      refine (ih hb').trans (SimpleGraph.Adj.reachable ?_)
      refine ⟨?_,e,hor⟩
      intro heq
      rcases hor with h | h
      · exact copy_loopless D P marked e (h.1.trans (heq.trans h.2.symm))
      · exact copy_loopless D P marked e (h.2.trans (heq.symm.trans h.1.symm))
  exact lift u.val v.val hr u.property v.property

/-- Full source connectivity uses the original domain hypothesis and preserves every copy. -/
theorem augmented_connected
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected) (u v : Vertex D P) :
    (augmentedGraph (sourceGraph D P marked) (alpha D P) (beta D P)).reaches Finset.univ u v := by
  have hr := Repair8.graph_reaches D P hD marked u v
  induction hr with
  | refl => exact .refl
  | @tail v w _ hadj ih =>
    obtain ⟨e,_,hor⟩ := hadj
    exact ih.tail ⟨.inl e,Finset.mem_univ _,hor⟩

/-- At a regular vertex, every physical incident face is on the chosen copy or one
other original copy sharing a genuine whole-arc face with it. -/
theorem source_regular_star_one_neighbor
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (Q : PlaneEmbedding (sourceGraph D P marked))
    (A : OuterArc Q (alpha D P) (beta D P))
    (x : {x : D // x ∉ P.val}) (e : Copy D P marked)
    (he : copyA D P marked e = .inr x ∨ copyB D P marked e = .inr x)
    (F : A.embedding.Face) (hF : A.embedding.incident (.inr x) F) :
    F ∈ edgeFaces A.embedding.drawing (.inl e) ∨
      ∃ q : Copy D P marked, q ≠ e ∧
        (copyA D P marked q = .inr x ∨ copyB D P marked q = .inr x) ∧
        F ∈ edgeFaces A.embedding.drawing (.inl q) ∧
        ∃ G : A.embedding.Face,
          G ∈ edgeFaces A.embedding.drawing (.inl e) ∩ edgeFaces A.embedding.drawing (.inl q) := by
  let J := augmentedGraph (sourceGraph D P marked) (alpha D P) (beta D P)
  have loopless (q : Copy D P marked ⊕ Unit) : J.left q ≠ J.right q := by
    cases q with
    | inl q => exact copy_loopless D P marked q
    | inr q => cases q; simp [J,augmentedGraph,alpha,beta]
  have hcover := four_copy_bond_face_cover J A.embedding.drawing A.embedding.edgeChart loopless
    (augmented_connected D P marked hD) (.inr x)
    (by
      intro u v hu hv
      convert augmented_reaches_without_regular D P marked x u v hu hv using 1
      ext q
      simp [J])
    (by
      convert augmented_regular_star_card D P marked x using 1
      congr 1
      ext q
      simp [J]) (.inl e) he F hF
  rcases hcover with h | ⟨q,hqe,hqx,hqF,G,hG⟩
  · exact Or.inl h
  · cases q with
    | inl q => exact Or.inr ⟨q,fun h => hqe (congrArg Sum.inl h),hqx,hqF,G,hG⟩
    | inr q => cases q; exact (hqx.elim
        (closing_arc_not_regular D P marked x).1 (closing_arc_not_regular D P marked x).2).elim

/-- The edge-square's face names are exactly the chart faces consumed in the bond. -/
theorem physical_edgeFaces_iff (Q : PlaneEmbedding (sourceGraph D P marked))
    (A : OuterArc Q (alpha D P) (beta D P)) (e : Copy D P marked) (F : A.embedding.Face) :
    F ∈ edgeFaces A.embedding.drawing (.inl e) ↔
      F = A.embedding.leftFace (.inl e) ∨ F = A.embedding.rightFace (.inl e) :=
  edgeFaces_iff_chart A.embedding.drawing (.inl e) (A.embedding.edgeChart (.inl e))
    (copy_loopless D P marked e) F

/-- An endpoint paired with either actual chart-face height is a literal square corner. -/
theorem incident_face_square_corner (Q : PlaneEmbedding (sourceGraph D P marked))
    (A : OuterArc Q (alpha D P) (beta D P)) (phi : Vertex D P → ℝ)
    (psi : A.embedding.Face → ℝ) (x : Vertex D P) (e : Copy D P marked)
    (he : copyA D P marked e = x ∨ copyB D P marked e = x)
    (F : A.embedding.Face) (hF : F ∈ edgeFaces A.embedding.drawing (.inl e)) :
    (phi x,psi F) ∈ edgeSquare Q (alpha D P) (beta D P) A phi psi e := by
  have hf := (physical_edgeFaces_iff D P marked Q A e F).mp hF
  constructor
  · rcases he with he | he
    · rw [← he]
      exact ⟨min_le_left _ _,le_max_left _ _⟩
    · rw [← he]
      exact ⟨min_le_right _ _,le_max_right _ _⟩
  · rcases hf with rfl | rfl
    · exact ⟨min_le_left _ _,le_max_left _ _⟩
    · exact ⟨min_le_right _ _,le_max_right _ _⟩

/-- The actual selected incident-face point lies in the chosen square, or in one
neighboring original square with a common physical corner. This includes point squares. -/
theorem source_regular_square_one_neighbor
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (Q : PlaneEmbedding (sourceGraph D P marked))
    (A : OuterArc Q (alpha D P) (beta D P)) (phi : Vertex D P → ℝ)
    (psi : A.embedding.Face → ℝ) (x : {x : D // x ∉ P.val}) (e : Copy D P marked)
    (he : copyA D P marked e = .inr x ∨ copyB D P marked e = .inr x)
    (F : A.embedding.Face) (hF : A.embedding.incident (.inr x) F) :
    (phi (.inr x),psi F) ∈ edgeSquare Q (alpha D P) (beta D P) A phi psi e ∨
      ∃ q : Copy D P marked, q ≠ e ∧
        (copyA D P marked q = .inr x ∨ copyB D P marked q = .inr x) ∧
        (phi (.inr x),psi F) ∈ edgeSquare Q (alpha D P) (beta D P) A phi psi q ∧
        ∃ G : A.embedding.Face,
          (phi (.inr x),psi G) ∈ edgeSquare Q (alpha D P) (beta D P) A phi psi e ∩
            edgeSquare Q (alpha D P) (beta D P) A phi psi q := by
  rcases source_regular_star_one_neighbor D P marked hD Q A x e he F hF with
      h | ⟨q,hqe,hqx,hqF,G,hGe,hGq⟩
  · exact Or.inl (incident_face_square_corner D P marked Q A phi psi (.inr x) e he F h)
  · exact Or.inr ⟨q,hqe,hqx,incident_face_square_corner D P marked Q A phi psi (.inr x) q hqx F hqF,
      G,incident_face_square_corner D P marked Q A phi psi (.inr x) e he G hGe,
      incident_face_square_corner D P marked Q A phi psi (.inr x) q hqx G hGq⟩

end
end FiniteAvalanches.Electrical.Plane.SourceLattice.CurrentRegularPhysical
