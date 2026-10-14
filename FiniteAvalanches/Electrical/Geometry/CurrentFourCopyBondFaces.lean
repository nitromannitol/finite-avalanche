import FiniteAvalanches.Electrical.Geometry.CurrentChartFaces
import FiniteAvalanches.External.PlaneDualBondCycle
import FiniteAvalanches.External.PlaneVertexFaceStar

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.BSST.CurrentBondFaces
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open CurrentChartFaces
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

/-- A literal four-copy singleton bond covers every actual incident face in one other edge. -/
theorem four_copy_bond_face_cover (J : CopiedGraph V E) (Q : Drawing J)
    (charts : ∀ e, EdgeChart Q e) (loopless : ∀ e, J.left e ≠ J.right e)
    (connected : ∀ u v, J.reaches Finset.univ u v) (x : V)
    (complement : ∀ u v, u ≠ x → v ≠ x →
      J.reaches (Finset.univ.filter fun e => J.left e ≠ x ∧ J.right e ≠ x) u v)
    (star_card : (Finset.univ.filter fun e => J.left e = x ∨ J.right e = x).card = 4)
    (e : E) (he : J.left e = x ∨ J.right e = x) (F : Face Q)
    (hF : incident Q x F) :
    F ∈ edgeFaces Q e ∨ ∃ q : E, q ≠ e ∧ (J.left q = x ∨ J.right q = x) ∧
      F ∈ edgeFaces Q q ∧ ∃ G : Face Q, G ∈ edgeFaces Q e ∩ edgeFaces Q q := by
  classical
  letI : Nonempty E := ⟨e⟩
  have hcut (q : E) :
      ((J.left q ∈ ({x} : Finset V) ∧ J.right q ∉ ({x} : Finset V)) ∨
        (J.right q ∈ ({x} : Finset V) ∧ J.left q ∉ ({x} : Finset V))) ↔
      J.left q = x ∨ J.right q = x := by
    simp only [Finset.mem_singleton]
    constructor
    · tauto
    · intro hi
      rcases hi with hi | hi
      · exact Or.inl ⟨hi,fun h => loopless q (hi.trans h.symm)⟩
      · exact Or.inr ⟨hi,fun h => loopless q (h.trans hi.symm)⟩
  have inside : ∀ u v : V, u ∈ ({x} : Finset V) → v ∈ ({x} : Finset V) →
      J.reaches (Finset.univ.filter fun q => J.left q ∈ ({x} : Finset V) ∧
        J.right q ∈ ({x} : Finset V)) u v := by
    intro u v hu hv
    have huv : u = v := (Finset.mem_singleton.mp hu).trans (Finset.mem_singleton.mp hv).symm
    rw [huv]
    exact .refl
  have outside : ∀ u v : V, u ∉ ({x} : Finset V) → v ∉ ({x} : Finset V) →
      J.reaches (Finset.univ.filter fun q => J.left q ∉ ({x} : Finset V) ∧
        J.right q ∉ ({x} : Finset V)) u v := by
    simpa only [Finset.mem_singleton] using complement
  obtain ⟨m,vertices,hinj,copies,hcard,hrows,hends⟩ :=
    FiniteAvalanches.External.finite_plane_dual_bond_cycle J Q charts {x} inside outside e
      ((hcut e).mpr he)
  have hc : m+1 = 4 := by simpa only [hcut,star_card] using hcard
  have hm : m = 3 := by omega
  subst m
  have row_faces (i : Fin 3) :
      vertices i.castSucc ∈ edgeFaces Q (copies i).val ∧
      vertices i.succ ∈ edgeFaces Q (copies i).val := by
    have hi := hrows i
    rcases hi with ⟨hn,hp⟩ | ⟨hp,hn⟩
    · constructor
      · exact (edgeFaces_iff_chart Q _ _ (loopless _) _).mpr (Or.inr hn.symm)
      · exact (edgeFaces_iff_chart Q _ _ (loopless _) _).mpr (Or.inl hp.symm)
    · constructor
      · exact (edgeFaces_iff_chart Q _ _ (loopless _) _).mpr (Or.inl hp.symm)
      · exact (edgeFaces_iff_chart Q _ _ (loopless _) _).mpr (Or.inr hn.symm)
  have end_faces : vertices 0 ∈ edgeFaces Q e ∧ vertices 3 ∈ edgeFaces Q e := by
    rcases hends with ⟨hn,hp⟩ | ⟨hp,hn⟩
    · exact ⟨(edgeFaces_iff_chart Q _ _ (loopless _) _).mpr (Or.inr hn.symm),
        (edgeFaces_iff_chart Q _ _ (loopless _) _).mpr (Or.inl hp.symm)⟩
    · exact ⟨(edgeFaces_iff_chart Q _ _ (loopless _) _).mpr (Or.inl hp.symm),
        (edgeFaces_iff_chart Q _ _ (loopless _) _).mpr (Or.inr hn.symm)⟩
  have cover (i : Fin 4) :
      vertices i ∈ edgeFaces Q e ∨ ∃ q : E, q ≠ e ∧ (J.left q = x ∨ J.right q = x) ∧
        vertices i ∈ edgeFaces Q q ∧ ∃ G : Face Q, G ∈ edgeFaces Q e ∩ edgeFaces Q q := by
    fin_cases i
    · exact Or.inl end_faces.1
    · exact Or.inr ⟨(copies 0).val,(copies 0).property.1,
        (hcut _).mp (copies 0).property.2,(row_faces 0).2,
        vertices 0,end_faces.1,(row_faces 0).1⟩
    · exact Or.inr ⟨(copies 2).val,(copies 2).property.1,
        (hcut _).mp (copies 2).property.2,(row_faces 2).1,
        vertices 3,end_faces.2,(row_faces 2).2⟩
    · exact Or.inl end_faces.2
  obtain ⟨q,hqx,hqF⟩ :=
    (FiniteAvalanches.External.plane_vertex_face_star V E J Q connected x).2.2.1 F |>.mp hF
  by_cases hqe : q = e
  · exact Or.inl (hqe ▸ hqF)
  · let qcut : {q : E // q ≠ e ∧
        ((J.left q ∈ ({x} : Finset V) ∧ J.right q ∉ ({x} : Finset V)) ∨
        (J.right q ∈ ({x} : Finset V) ∧ J.left q ∉ ({x} : Finset V)))} :=
      ⟨q,hqe,(hcut q).mpr hqx⟩
    obtain ⟨i,hi⟩ := copies.surjective qcut
    have hiq : (copies i).val = q := congrArg Subtype.val hi
    have hside := (edgeFaces_iff_chart Q q (charts q) (loopless q) F).mp hqF
    have hrow := hrows i
    rw [hiq] at hrow
    have hex : ∃ k : Fin 4, F = vertices k := by
      rcases hrow with ⟨hn,hp⟩ | ⟨hp,hn⟩
      · rcases hside with hpF | hnF
        · exact ⟨i.succ,hpF.trans hp⟩
        · exact ⟨i.castSucc,hnF.trans hn⟩
      · rcases hside with hpF | hnF
        · exact ⟨i.castSucc,hpF.trans hp⟩
        · exact ⟨i.succ,hnF.trans hn⟩
    obtain ⟨k,rfl⟩ := hex
    exact cover k

end
end FiniteAvalanches.Electrical.BSST.CurrentBondFaces
