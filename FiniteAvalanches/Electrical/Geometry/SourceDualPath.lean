import FiniteAvalanches.Electrical.Geometry.SourceAlphaCopies

/-! Original-copy source path in the dual of H, conditional on one closed classical formula. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeDrawing
open LatticeProb
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST
open FiniteAvalanches.Electrical.Plane.SourceLattice
open FiniteAvalanches.Electrical.LatticeCell
open scoped Classical
noncomputable section

/-- The original H0 alpha copies form a simple path on the full H dual face carrier,
conditional only on the explicit generic bond-to-cycle proposition. -/
theorem source_deleted_dual_path_of_bond_cycle
    (hbond :
∀ {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (Q : Drawing J)
    (charts : ∀ e : E, EdgeChart Q e) (A : Finset V),
  (∀ x y : V, x ∈ A → y ∈ A →
    J.reaches (Finset.univ.filter fun e => J.left e ∈ A ∧ J.right e ∈ A) x y) →
  (∀ x y : V, x ∉ A → y ∉ A →
    J.reaches (Finset.univ.filter fun e => J.left e ∉ A ∧ J.right e ∉ A) x y) →
  ∀ marked : E,
    ((J.left marked ∈ A ∧ J.right marked ∉ A) ∨
      (J.right marked ∈ A ∧ J.left marked ∉ A)) →
  ∃ m : ℕ, ∃ vertices : Fin (m + 1) → Face Q,
    Function.Injective vertices ∧
    ∃ copies : Fin m ≃ {e : E // e ≠ marked ∧
      ((J.left e ∈ A ∧ J.right e ∉ A) ∨ (J.right e ∈ A ∧ J.left e ∉ A))},
      m + 1 = (Finset.univ.filter fun e : E =>
        (J.left e ∈ A ∧ J.right e ∉ A) ∨ (J.right e ∈ A ∧ J.left e ∉ A)).card ∧
      (∀ i : Fin m,
        (negativeChartFace Q (copies i).val (charts (copies i).val) = vertices i.castSucc ∧
          positiveChartFace Q (copies i).val (charts (copies i).val) = vertices i.succ) ∨
        (positiveChartFace Q (copies i).val (charts (copies i).val) = vertices i.castSucc ∧
          negativeChartFace Q (copies i).val (charts (copies i).val) = vertices i.succ)) ∧
      ((negativeChartFace Q marked (charts marked) = vertices 0 ∧
          positiveChartFace Q marked (charts marked) = vertices (Fin.last m)) ∨
        (positiveChartFace Q marked (charts marked) = vertices 0 ∧
          negativeChartFace Q marked (charts marked) = vertices (Fin.last m))))
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) :
    ∃ q : Plane → Plane, Continuous q ∧ ∃ Q : Drawing (primalGraph D P),
      (∀ v : D, Q.point (project D P v.val) = q (sitePoint v.val)) ∧
      (∀ e t, Q.curve e t = q (unitSegment e.val.1 e.val.2 t.val)) ∧
      ∃ charts : ∀ e, EdgeChart Q e,
      ∃ finiteFaces : Fintype (Face Q),
        letI : Fintype (Face Q) := finiteFaces
        ∃ dualDrawing : Drawing (sourceDualGraph D P Q charts),
        ∃ dualCharts : ∀ e, EdgeChart dualDrawing e,
        ∃ vertexFaces : Vertex D P ≃ Face dualDrawing,
          (∀ F : Face Q, dualDrawing.point F ∈ faceRegion Q F) ∧
          (∀ v : Vertex D P, Q.point v ∈ faceRegion dualDrawing (vertexFaces v)) ∧
          (∀ (e f : PrimalCopy D P) (s t : ArcParameter),
            Q.curve e s = dualDrawing.curve f t ↔
              e = f ∧ s.val = 1 / 2 ∧ t.val = 1 / 2) ∧
          (∀ (e : PrimalCopy D P) (t : ArcParameter),
            (t.val < 1 / 2 → dualDrawing.curve e t ∈
              faceRegion Q ((sourceDualGraph D P Q charts).left e)) ∧
            (1 / 2 < t.val → dualDrawing.curve e t ∈
              faceRegion Q ((sourceDualGraph D P Q charts).right e))) ∧
          (∀ e : PrimalCopy D P, ∃ radius : ℝ, 0 < radius ∧
            radius < (charts e).radius ∧ ∀ t : ArcParameter,
              |t.val - 1 / 2| < radius →
              (charts e).chart.map (dualDrawing.curve e t) = (1 / 2, t.val - 1 / 2)) ∧
          (∀ e : PrimalCopy D P,
            positiveChartFace dualDrawing e (dualCharts e) = vertexFaces ((primalGraph D P).left e) ∧
            negativeChartFace dualDrawing e (dualCharts e) = vertexFaces ((primalGraph D P).right e)) ∧
          ∃ Hstar : Drawing (sourceDeletedDualGraph D P marked Q charts),
            (∀ F : Face Q, Hstar.point F = dualDrawing.point F) ∧
            (∀ e t, Hstar.curve e t = dualDrawing.curve (retainedPrimal D P marked e) t) ∧
            ∃ m : ℕ, 3 ≤ m ∧ ∃ vertices : Fin (m + 1) → Face Q,
              Function.Injective vertices ∧
              ∃ copies : Fin m ≃ {e : Copy D P marked //
                copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P},
                (∀ i : Fin m,
                  ((sourceDeletedDualGraph D P marked Q charts).left (copies i).val = vertices i.castSucc ∧
                    (sourceDeletedDualGraph D P marked Q charts).right (copies i).val = vertices i.succ) ∨
                  ((sourceDeletedDualGraph D P marked Q charts).right (copies i).val = vertices i.castSucc ∧
                    (sourceDeletedDualGraph D P marked Q charts).left (copies i).val = vertices i.succ)) ∧
                (((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices 0 ∧
                    (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices (Fin.last m)) ∨
                  ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices 0 ∧
                    (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices (Fin.last m))) := by
  obtain ⟨q, hq, Q, hp, hc, charts, finiteFaces, hdual⟩ :=
    source_H_deleted_dual_realization D P hD hDc hP marked
  letI : Fintype (Face Q) := finiteFaces
  obtain ⟨dualDrawing, dualCharts, vertexFaces, hpoint, hvertex, hcross,
    hparts, hlocal, horient, Hstar, hsp, hsc⟩ := hdual
  have hmark : ((primalGraph D P).left (markedPrimal D P marked) ∈
        ({alpha D P} : Finset (Vertex D P)) ∧
      (primalGraph D P).right (markedPrimal D P marked) ∉
        ({alpha D P} : Finset (Vertex D P))) ∨
      ((primalGraph D P).right (markedPrimal D P marked) ∈
        ({alpha D P} : Finset (Vertex D P)) ∧
      (primalGraph D P).left (markedPrimal D P marked) ∉
        ({alpha D P} : Finset (Vertex D P))) := by
    simp only [Finset.mem_singleton]
    apply (alpha_cut_iff D P _).mpr
    exact marked.property.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
  obtain ⟨m, vertices, hinj, edges, hcard, hends, hmarked⟩ :=
    hbond (primalGraph D P) Q charts {alpha D P}
      (by
        intro x y hx hy
        rw [Finset.mem_singleton] at hx hy
        subst x
        subst y
        exact .refl)
      (by
        intro x y hx hy
        simp only [Finset.mem_singleton] at hx hy ⊢
        exact primal_reaches_without_alpha D P hD x y hx hy)
      (markedPrimal D P marked) hmark
  simp only [Finset.mem_singleton] at hcard
  have hm : 3 ≤ m := by
    have hfour := alpha_star_card_ge_four D P
    have heq : (Finset.univ.filter fun e : PrimalCopy D P =>
        ((primalGraph D P).left e = alpha D P ∧ (primalGraph D P).right e ≠ alpha D P) ∨
        ((primalGraph D P).right e = alpha D P ∧ (primalGraph D P).left e ≠ alpha D P)) =
        (Finset.univ.filter fun e : PrimalCopy D P =>
          (primalGraph D P).left e = alpha D P ∨ (primalGraph D P).right e = alpha D P) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, alpha_cut_iff]
    rw [heq] at hcard
    omega
  let copies := (edges.trans (alphaSingletonCutEquiv D P marked)).trans
    (retainedAlphaEquiv D P marked)
  refine ⟨q, hq, Q, hp, hc, charts, finiteFaces, dualDrawing, dualCharts, vertexFaces,
    hpoint, hvertex, hcross, hparts, hlocal, horient, Hstar, hsp, hsc,
    m, hm, vertices, hinj, copies, ?_, hmarked⟩
  intro i
  exact hends i

end
end FiniteAvalanches.Electrical.LatticeDrawing
