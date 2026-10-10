import FiniteAvalanches.Electrical.Geometry.FiniteLatticeDrawing
import FiniteAvalanches.Electrical.Geometry.FiniteConnectedSpan
import FiniteAvalanches.Electrical.Geometry.SourceChartApplication

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeDrawing
open LatticeProb
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.Plane.SourceLattice
open FiniteAvalanches.Electrical.DrawingContraction
open FiniteAvalanches.Electrical.LatticeCell
open scoped Classical
noncomputable section

theorem fiber_reaches_symm {V E W : Type} (J : CopiedGraph V E) (p : V → W)
    {x y : V} (h : Relation.ReflTransGen (fiberStep J p) x y) :
    Relation.ReflTransGen (fiberStep J p) y x := by
  induction h with
  | refl => exact .refl
  | @tail y z _ hs ih =>
    obtain ⟨he, e, hor⟩ := hs
    apply Relation.ReflTransGen.trans _ ih
    refine .single ⟨he.symm, e, ?_⟩
    exact hor.elim (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩)

theorem lift_lattice_fiber {W : Type} (U : Finset (Site 2)) (p : U → W)
    (C : Set (Site 2)) (hCU : C ⊆ (↑U : Set (Site 2))) (w : W)
    (hp : ∀ x (hx : x ∈ C), p ⟨x, hCU hx⟩ = w)
    {x y : Site 2} (hx : x ∈ C) (hy : y ∈ C)
    (h : Relation.ReflTransGen (fun a b => a ∈ C ∧ b ∈ C ∧ (lattice 2).Adj a b) x y) :
    Relation.ReflTransGen (fiberStep (finiteLatticeGraph U) p)
      ⟨x, hCU hx⟩ ⟨y, hCU hy⟩ := by
  induction h with
  | refl => exact .refl
  | @tail y z _ hs ih =>
    obtain ⟨hy', hz, i, hor⟩ := hs
    apply (ih hy').tail
    refine ⟨(hp y hy').trans (hp z hz).symm, ?_⟩
    rcases hor with he | he
    · refine ⟨⟨(y, i), (mem_latticeCopies U (y, i)).mpr ⟨hCU hy', ?_⟩⟩, Or.inl ⟨rfl, ?_⟩⟩
      · change y + unit i ∈ U
        rw [← he]
        exact hCU hz
      · exact Subtype.ext he.symm
    · refine ⟨⟨(z, i), (mem_latticeCopies U (z, i)).mpr ⟨hCU hz, ?_⟩⟩, Or.inr ⟨?_, rfl⟩⟩
      · change z + unit i ∈ U
        rw [← he]
        exact hCU hy'
      · exact Subtype.ext he.symm

theorem source_primal_realization (D : Finset (Site 2)) (P : OneSet D)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) :
    ∃ q : Plane → Plane, Continuous q ∧ ∃ Q : Drawing
      (⟨fun e : ↥((domainCopies D).filter (fun e =>
      project D P (originalA e) ≠ project D P (originalB e))) => project D P (originalA e.val),
      fun e => project D P (originalB e.val)⟩ :
      CopiedGraph (Vertex D P) ↥((domainCopies D).filter (fun e =>
        project D P (originalA e) ≠ project D P (originalB e)))),
      (∀ v : D, Q.point (project D P v.val) = q (sitePoint v.val)) ∧
      (∀ e t, Q.curve e t = q (unitSegment e.val.1 e.val.2 t.val)) := by
  let N := ((domainCopies D).image originalA ∪ (domainCopies D).image originalB).filter
    (fun x => x ∉ D)
  have hN : (↑N : Set (Site 2)) ⊆ (↑D : Set (Site 2))ᶜ := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hex : ∃ r : Site 2, r ∉ D := by
    rcases marked.property with h | h
    · exact ⟨originalA marked.val, (project_eq_alpha_iff D P _).mp h.1⟩
    · exact ⟨originalB marked.val, (project_eq_alpha_iff D P _).mp h.2⟩
  obtain ⟨r, hr⟩ := hex
  obtain ⟨C, hNC, hCD, hrC, hCr⟩ := finite_connected_span (lattice 2)
    (↑D : Set (Site 2))ᶜ hDc N hN r hr
  let U : Finset (Site 2) := D ∪ C
  have hDU : (↑D : Set (Site 2)) ⊆ (↑U : Set (Site 2)) :=
    fun _ hx => Finset.mem_union_left _ hx
  have hCU : (↑C : Set (Site 2)) ⊆ (↑U : Set (Site 2)) :=
    fun _ hx => Finset.mem_union_right _ hx
  have hPU : (↑(P.val.image Subtype.val) : Set (Site 2)) ⊆ (↑U : Set (Site 2)) := by
    intro x hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact hDU v.property
  let p : U → Vertex D P := fun v => project D P v.val
  have halpha (x : Site 2) (hx : x ∈ C) : p ⟨x, hCU hx⟩ = alpha D P :=
    (project_eq_alpha_iff D P x).mpr (hCD hx)
  have hbeta (x : Site 2) (hx : x ∈ P.val.image Subtype.val) :
      p ⟨x, hPU hx⟩ = beta D P := (project_eq_beta_iff D P x).mpr hx
  have hsurj : Function.Surjective p := by
    intro w
    cases w with
    | inl b =>
      cases b with
      | false => exact ⟨⟨r, hCU hrC⟩, halpha r hrC⟩
      | true =>
        obtain ⟨x, hx⟩ := P.property
        exact ⟨⟨x.val, hDU x.property⟩,
          (project_eq_beta_iff D P x.val).mpr (Finset.mem_image.mpr ⟨x, hx, rfl⟩)⟩
    | inr x => exact ⟨⟨x.val.val, hDU x.val.property⟩, project_free D P x⟩
  have hconn : ∀ x y : U, p x = p y →
      Relation.ReflTransGen (fiberStep (finiteLatticeGraph U) p) x y := by
    intro x y hxy
    cases he : p x with
    | inl b =>
      have hey : p y = .inl b := hxy.symm.trans he
      cases b with
      | false =>
        have hxD : x.val ∉ D := (project_eq_alpha_iff D P x.val).mp he
        have hyD : y.val ∉ D := (project_eq_alpha_iff D P y.val).mp hey
        have hxC : x.val ∈ C := (Finset.mem_union.mp x.property).resolve_left hxD
        have hyC : y.val ∈ C := (Finset.mem_union.mp y.property).resolve_left hyD
        have hxR := lift_lattice_fiber U p (↑C : Set (Site 2)) hCU (alpha D P)
          halpha hrC hxC (hCr x.val hxC)
        have hyR := lift_lattice_fiber U p (↑C : Set (Site 2)) hCU (alpha D P)
          halpha hrC hyC (hCr y.val hyC)
        exact (fiber_reaches_symm _ _ hxR).trans hyR
      | true =>
        have hxP : x.val ∈ P.val.image Subtype.val := (project_eq_beta_iff D P x.val).mp he
        have hyP : y.val ∈ P.val.image Subtype.val := (project_eq_beta_iff D P y.val).mp hey
        exact lift_lattice_fiber U p (↑(P.val.image Subtype.val) : Set (Site 2)) hPU
          (beta D P) hbeta hxP hyP
          (induced_reaches (↑(P.val.image Subtype.val) : Set (Site 2)) hP _ _ hxP hyP)
    | inr v =>
      have hx : x.val = v.val.val := (project_eq_free_iff D P v x.val).mp he
      have hy : y.val = v.val.val := (project_eq_free_iff D P v y.val).mp (hxy.symm.trans he)
      have hv : x = y := Subtype.ext (hx.trans hy.symm)
      exact hv ▸ Relation.ReflTransGen.refl
  obtain ⟨q, hq, Q, hp, hc⟩ := connected_quotient (finiteLatticeGraph U)
    (finiteLatticeDrawing U) p hsurj hconn
  letI : Fintype {f : ↥(latticeCopies U) //
      p ((finiteLatticeGraph U).left f) ≠ p ((finiteLatticeGraph U).right f)} :=
    @Subtype.fintype ↥(latticeCopies U)
      (fun f => p ((finiteLatticeGraph U).left f) ≠ p ((finiteLatticeGraph U).right f))
      (fun f => @instDecidableNot
        (p ((finiteLatticeGraph U).left f) = p ((finiteLatticeGraph U).right f))
        (Classical.propDecidable _)) inferInstance
  have endpoints (e : OriginalCopy) (he : e ∈ domainCopies D) :
      originalA e ∈ U ∧ originalB e ∈ U := by
    have incl (x : Site 2) (hx : x ∈ (domainCopies D).image originalA ∪
        (domainCopies D).image originalB) : x ∈ U := by
      by_cases hxD : x ∈ D
      · exact hDU hxD
      · exact hCU (hNC (Finset.mem_filter.mpr ⟨hx, hxD⟩))
    exact ⟨incl _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)),
      incl _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, rfl⟩))⟩
  let i (e : ↥((domainCopies D).filter (fun e =>
      project D P (originalA e) ≠ project D P (originalB e)))) :
      {f : ↥(latticeCopies U) //
        p ((finiteLatticeGraph U).left f) ≠ p ((finiteLatticeGraph U).right f)} :=
    ⟨⟨e.val, (mem_latticeCopies U e.val).mpr
      (endpoints e.val (Finset.mem_filter.mp e.property).1)⟩,
      (Finset.mem_filter.mp e.property).2⟩
  have hi : Function.Injective i := by
    intro e f h
    exact Subtype.ext (congrArg (fun z => z.val.val) h)
  refine ⟨q, hq, restrictDrawing Q i hi (fun _ => rfl) (fun _ => rfl), ?_, ?_⟩
  · intro v
    exact hp ⟨v.val, hDU v.property⟩
  · intro e t
    exact hc (i e) t

theorem source_primal_drawing (D : Finset (Site 2)) (P : OneSet D)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) :
    Nonempty (Drawing (⟨fun e : ↥((domainCopies D).filter (fun e =>
      project D P (originalA e) ≠ project D P (originalB e))) => project D P (originalA e.val),
      fun e => project D P (originalB e.val)⟩ :
      CopiedGraph (Vertex D P) ↥((domainCopies D).filter (fun e =>
        project D P (originalA e) ≠ project D P (originalB e))))) := by
  obtain ⟨_, _, Q, _, _⟩ := source_primal_realization D P hDc hP marked
  exact ⟨Q⟩

theorem source_H0_drawing (D : Finset (Site 2)) (P : OneSet D)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) :
    Nonempty (Drawing (⟨copyA D P marked, copyB D P marked⟩ :
      CopiedGraph (Vertex D P) (Copy D P marked))) := by
  obtain ⟨Q⟩ := source_primal_drawing D P hDc hP marked
  let i (e : Copy D P marked) : ↥((domainCopies D).filter (fun e =>
      project D P (originalA e) ≠ project D P (originalB e))) :=
    ⟨e.val, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp e.property).1,
      (Finset.mem_filter.mp e.property).2.1⟩⟩
  have hi : Function.Injective i := by
    intro e f h
    have hv := congrArg Subtype.val h
    exact Subtype.ext hv
  exact ⟨restrictDrawing Q i hi
    (fun _ => rfl) (fun _ => rfl)⟩

theorem source_H0_planeEmbedding (D : Finset (Site 2)) (P : OneSet D)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) :
    Nonempty (PlaneEmbedding (⟨copyA D P marked, copyB D P marked⟩ :
      CopiedGraph (Vertex D P) (Copy D P marked))) := by
  obtain ⟨Q⟩ := source_H0_drawing D P hDc hP marked
  obtain ⟨charts⟩ := ChartExistence.consume_arc_straightening
    FiniteAvalanches.External.parametrized_plane_arc_straightening Q (copy_loopless D P marked)
  exact ⟨ChartExistence.planeEmbeddingOfCharts Q (copy_loopless D P marked) charts⟩

end
end FiniteAvalanches.Electrical.LatticeDrawing
