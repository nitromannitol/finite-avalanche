import FiniteAvalanches.Electrical.Geometry.SourceDualPath
import FiniteAvalanches.Electrical.Geometry.ComplementFaces

/-! The actual retained source path and the complement face containing both primal poles. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeDrawing
open LatticeProb
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST
open FiniteAvalanches.Electrical.Plane.SourceLattice
open FiniteAvalanches.Electrical.LatticeCell
open FiniteAvalanches.Electrical.ComplementFaces
open scoped Classical
noncomputable section

/-- The actual simple retained path coexists with one uniquely determined complement
face containing both primal poles and the whole original marked primal arc.
The only open antecedent is the explicitly written closed bond-cycle formula. -/
theorem source_path_face_merger_of_bond_cycle
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
            ∃ merged : Face Hstar,
              Q.point (alpha D P) ∈ faceRegion Hstar merged ∧
              Q.point (beta D P) ∈ faceRegion Hstar merged ∧
              Set.range (Q.curve (markedPrimal D P marked)) ⊆ faceRegion Hstar merged ∧
              faceRegion dualDrawing (vertexFaces (alpha D P)) ⊆ faceRegion Hstar merged ∧
              faceRegion dualDrawing (vertexFaces (beta D P)) ⊆ faceRegion Hstar merged ∧
              (∀ face : Face Hstar,
                Q.point (alpha D P) ∈ faceRegion Hstar face → face = merged) ∧
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
    source_deleted_dual_path_of_bond_cycle hbond D P hD hDc hP marked
  letI : Fintype (Face Q) := finiteFaces
  obtain ⟨dualDrawing, dualCharts, vertexFaces, hpoint, hvertex, hcross,
    hparts, hlocal, horient, Hstar, hsp, hsc,
    m, hm, vertices, hinj, copies, hends, hmarked⟩ := hdual
  have htrace : drawingTrace Hstar ⊆ drawingTrace dualDrawing := by
    rintro z (⟨v, hv⟩ | hz)
    · exact Or.inl ⟨v, (hsp v).symm.trans hv⟩
    · obtain ⟨e, t, ht⟩ := Set.mem_iUnion.mp hz
      exact Or.inr (Set.mem_iUnion.mpr
        ⟨retainedPrimal D P marked e, t, (hsc e t).symm.trans ht⟩)
  have hoff (s : ArcParameter) :
      Q.curve (markedPrimal D P marked) s ∉ drawingTrace Hstar := by
    rintro (⟨v, hv⟩ | hz)
    · obtain ⟨ho, _⟩ := hpoint v
      apply ho
      exact Or.inr (Set.mem_iUnion.mpr
        ⟨markedPrimal D P marked, s, hv.symm.trans (hsp v)⟩)
    · obtain ⟨e, t, ht⟩ := Set.mem_iUnion.mp hz
      have he := (hcross (markedPrimal D P marked)
        (retainedPrimal D P marked e) s t).mp
          (ht.symm.trans (hsc e t))
      exact retainedPrimal_ne_marked D P marked e he.1.symm
  obtain ⟨merged, hinside, _, _⟩ := DeletedArc.common_face Hstar
    (Q.curve (markedPrimal D P marked)) (Q.continuous _) (fun t _ _ => hoff t)
  have hall : Set.range (Q.curve (markedPrimal D P marked)) ⊆
      faceRegion Hstar merged := by
    have hwhole := range_subset_faceAt Hstar (Q.curve (markedPrimal D P marked))
      (Q.continuous _) hoff
    have hmid := hinside ⟨1/2, by constructor <;> norm_num⟩
      (by norm_num) (by norm_num)
    have heq := face_eq_of_mem Hstar _ merged _
      (hwhole (Set.mem_range_self ⟨1/2, by constructor <;> norm_num⟩)) hmid
    exact heq ▸ hwhole
  have hab : Q.point (alpha D P) ∈ faceRegion Hstar merged ∧
      Q.point (beta D P) ∈ faceRegion Hstar merged := by
    have hs := hall ⟨⟨0, by constructor <;> norm_num⟩, Q.start _⟩
    have ht := hall ⟨⟨1, by constructor <;> norm_num⟩, Q.finish _⟩
    rcases marked.property with h | h
    · exact ⟨h.1 ▸ hs, h.2 ▸ ht⟩
    · exact ⟨h.2 ▸ ht, h.1 ▸ hs⟩
  have hregions (v : Vertex D P) (hv : Q.point v ∈ faceRegion Hstar merged) :
      faceRegion dualDrawing (vertexFaces v) ⊆ faceRegion Hstar merged := by
    obtain ⟨ho, he⟩ := hvertex v
    have hsub := faceRegion_subset_of_trace_subset dualDrawing Hstar htrace
      (Q.point v) ho
    change faceAt dualDrawing (Q.point v) ho = vertexFaces v at he
    rw [he] at hsub
    have hmerge := face_eq_of_mem Hstar _ merged (Q.point v)
      (mem_faceAt Hstar _ (fun h => ho (htrace h))) hv
    exact hmerge ▸ hsub
  refine ⟨q, hq, Q, hp, hc, charts, finiteFaces, dualDrawing, dualCharts, vertexFaces,
    hpoint, hvertex, hcross, hparts, hlocal, horient, Hstar, hsp, hsc,
    merged, hab.1, hab.2, hall, hregions _ hab.1, hregions _ hab.2, ?_,
    m, hm, vertices, hinj, copies, hends, hmarked⟩
  intro face hf
  exact face_eq_of_mem Hstar face merged (Q.point (alpha D P)) hf hab.1

/-- Deleting the original marked dual copy puts both primal poles, the whole marked
primal curve, and both corresponding full-dual face regions into one actual face.
This merger needs no bond-cycle antecedent. -/
theorem source_marked_dual_face_merger
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
            ∃ merged : Face Hstar,
              Q.point (alpha D P) ∈ faceRegion Hstar merged ∧
              Q.point (beta D P) ∈ faceRegion Hstar merged ∧
              Set.range (Q.curve (markedPrimal D P marked)) ⊆ faceRegion Hstar merged ∧
              faceRegion dualDrawing (vertexFaces (alpha D P)) ⊆ faceRegion Hstar merged ∧
              faceRegion dualDrawing (vertexFaces (beta D P)) ⊆ faceRegion Hstar merged ∧
              (∀ face : Face Hstar,
                Q.point (alpha D P) ∈ faceRegion Hstar face → face = merged) := by
  obtain ⟨q, hq, Q, hp, hc, charts, finiteFaces, hdual⟩ :=
    source_H_deleted_dual_realization D P hD hDc hP marked
  letI : Fintype (Face Q) := finiteFaces
  obtain ⟨dualDrawing, dualCharts, vertexFaces, hpoint, hvertex, hcross,
    hparts, hlocal, horient, Hstar, hsp, hsc⟩ := hdual
  have htrace : drawingTrace Hstar ⊆ drawingTrace dualDrawing := by
    rintro z (⟨v, hv⟩ | hz)
    · exact Or.inl ⟨v, (hsp v).symm.trans hv⟩
    · obtain ⟨e, t, ht⟩ := Set.mem_iUnion.mp hz
      exact Or.inr (Set.mem_iUnion.mpr
        ⟨retainedPrimal D P marked e, t, (hsc e t).symm.trans ht⟩)
  have hoff (s : ArcParameter) :
      Q.curve (markedPrimal D P marked) s ∉ drawingTrace Hstar := by
    rintro (⟨v, hv⟩ | hz)
    · obtain ⟨ho, _⟩ := hpoint v
      apply ho
      exact Or.inr (Set.mem_iUnion.mpr
        ⟨markedPrimal D P marked, s, hv.symm.trans (hsp v)⟩)
    · obtain ⟨e, t, ht⟩ := Set.mem_iUnion.mp hz
      have he := (hcross (markedPrimal D P marked)
        (retainedPrimal D P marked e) s t).mp
          (ht.symm.trans (hsc e t))
      exact retainedPrimal_ne_marked D P marked e he.1.symm
  obtain ⟨merged, hinside, _, _⟩ := DeletedArc.common_face Hstar
    (Q.curve (markedPrimal D P marked)) (Q.continuous _) (fun t _ _ => hoff t)
  have hall : Set.range (Q.curve (markedPrimal D P marked)) ⊆
      faceRegion Hstar merged := by
    have hwhole := range_subset_faceAt Hstar (Q.curve (markedPrimal D P marked))
      (Q.continuous _) hoff
    have hmid := hinside ⟨1/2, by constructor <;> norm_num⟩
      (by norm_num) (by norm_num)
    have heq := face_eq_of_mem Hstar _ merged _
      (hwhole (Set.mem_range_self ⟨1/2, by constructor <;> norm_num⟩)) hmid
    exact heq ▸ hwhole
  have hab : Q.point (alpha D P) ∈ faceRegion Hstar merged ∧
      Q.point (beta D P) ∈ faceRegion Hstar merged := by
    have hs := hall ⟨⟨0, by constructor <;> norm_num⟩, Q.start _⟩
    have ht := hall ⟨⟨1, by constructor <;> norm_num⟩, Q.finish _⟩
    rcases marked.property with h | h
    · exact ⟨h.1 ▸ hs, h.2 ▸ ht⟩
    · exact ⟨h.2 ▸ ht, h.1 ▸ hs⟩
  have hregions (v : Vertex D P) (hv : Q.point v ∈ faceRegion Hstar merged) :
      faceRegion dualDrawing (vertexFaces v) ⊆ faceRegion Hstar merged := by
    obtain ⟨ho, he⟩ := hvertex v
    have hsub := faceRegion_subset_of_trace_subset dualDrawing Hstar htrace
      (Q.point v) ho
    change faceAt dualDrawing (Q.point v) ho = vertexFaces v at he
    rw [he] at hsub
    have hmerge := face_eq_of_mem Hstar _ merged (Q.point v)
      (mem_faceAt Hstar _ (fun h => ho (htrace h))) hv
    exact hmerge ▸ hsub
  refine ⟨q, hq, Q, hp, hc, charts, finiteFaces, dualDrawing, dualCharts, vertexFaces,
    hpoint, hvertex, hcross, hparts, hlocal, horient, Hstar, hsp, hsc,
    merged, hab.1, hab.2, hall, hregions _ hab.1, hregions _ hab.2, ?_⟩
  intro face hf
  exact face_eq_of_mem Hstar face merged (Q.point (alpha D P)) hf hab.1


end
end FiniteAvalanches.Electrical.LatticeDrawing
