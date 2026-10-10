import FiniteAvalanches.Electrical.Geometry.SourceDualPath
import FiniteAvalanches.Electrical.Geometry.CopiedGraphPath

/-! Connectivity of the source dual after deleting one original copied edge. -/
namespace FiniteAvalanches.Electrical.LatticeDrawing
open LatticeProb
open FiniteAvalanches.Electrical
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST
open FiniteAvalanches.Electrical.Plane.SourceLattice
open FiniteAvalanches.Electrical.LatticeCell
open scoped Classical
noncomputable section

/-- The deleted dual is connected for the supplied Q and its supplied physical charts.
No different drawing or finite-face witness is chosen. -/
theorem source_deleted_dual_preconnected_of_classical
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (_hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (_hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P)
    (Q : Drawing (primalGraph D P)) (charts : ∀ e, EdgeChart Q e)
    (hdualConnected :
∀ {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
      (J : CopiedGraph V E) (D : Drawing J)
      (charts : ∀ e : E, Source.EdgeChart D e)
      (_hc : (supportGraph J.left J.right).Preconnected),
      let dualGraph : CopiedGraph (Face D) E :=
        ⟨fun e => negativeChartFace D e (charts e),
          fun e => positiveChartFace D e (charts e)⟩
      (supportGraph dualGraph.left dualGraph.right).Preconnected )
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
    : (supportGraph (sourceDeletedDualGraph D P marked Q charts).left
        (sourceDeletedDualGraph D P marked Q charts).right).Preconnected := by
  letI : DecidableEq (PrimalCopy D P) := Classical.decEq _
  have hmark :
      (((primalGraph D P).left (markedPrimal D P marked) ∈
          ({alpha D P} : Finset (Vertex D P)) ∧
        (primalGraph D P).right (markedPrimal D P marked) ∉
          ({alpha D P} : Finset (Vertex D P))) ∨
      ((primalGraph D P).right (markedPrimal D P marked) ∈
          ({alpha D P} : Finset (Vertex D P)) ∧
        (primalGraph D P).left (markedPrimal D P marked) ∉
          ({alpha D P} : Finset (Vertex D P)))) := by
    simp only [Finset.mem_singleton]
    apply (alpha_cut_iff D P _).mpr
    exact marked.property.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
  obtain ⟨m, vertices, _hinj, edges, _hcard, hends, hmarked⟩ :=
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
  let J := sourceDualGraph D P Q charts
  let K := sourceDeletedDualGraph D P marked Q charts
  let ids : Fin m → PrimalCopy D P := fun i => (edges i).val
  have hids : ∀ i : Fin m, ids i ∈ Finset.univ.erase (markedPrimal D P marked) := by
    intro i
    exact Finset.mem_erase.mpr ⟨(edges i).property.1, Finset.mem_univ _⟩
  have hwalk : J.reaches (Finset.univ.erase (markedPrimal D P marked))
      (vertices 0) (vertices (Fin.last m)) :=
    J.reaches_of_ordered_copies m vertices ids hids (fun i => hends i)
  change
    ((J.left (markedPrimal D P marked) = vertices 0 ∧
        J.right (markedPrimal D P marked) = vertices (Fin.last m)) ∨
      (J.right (markedPrimal D P marked) = vertices 0 ∧
        J.left (markedPrimal D P marked) = vertices (Fin.last m))) at hmarked
  have halt : J.reaches (Finset.univ.erase (markedPrimal D P marked))
      (J.left (markedPrimal D P marked)) (J.right (markedPrimal D P marked)) := by
    rcases hmarked with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · rw [hl, hr]
      exact hwalk
    · rw [hl, hr]
      exact J.grove_reaches_symm hwalk
  letI : Nonempty (PrimalCopy D P) := ⟨markedPrimal D P marked⟩
  have hconn : (supportGraph J.left J.right).Preconnected :=
    hdualConnected (primalGraph D P) Q charts (primal_preconnected D P hD marked)
  exact J.supportGraph_preconnected_of_erase_equiv K (markedPrimal D P marked)
    (retainedPrimalEquiv D P marked) (fun _ => rfl) (fun _ => rfl) hconn halt

end
end FiniteAvalanches.Electrical.LatticeDrawing
