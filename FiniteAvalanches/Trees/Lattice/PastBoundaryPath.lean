import FiniteAvalanches.Trees.FiniteCirculation
import FiniteAvalanches.Trees.Lattice.PastBoundaryCirculation
import FiniteAvalanches.Trees.Lattice.EuclideanPaths

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Lattice.PastTail
open LatticeProb SimpleGraph FiniteAvalanches.Trees
open scoped Classical BigOperators
noncomputable section

/-- Every original crossed past-boundary dual edge is on the actual selected
fundamental path or is the literal outgoing exception. Neither a boundary cycle
nor a boundary/path relationship is supplied as a hypothesis. -/
theorem vertexPast_dual_boundary_mem_path_or_outgoing (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (hDual : IsTree (dualField ω)) (v : Site 2)
    (p : Site 2 × Fin 2) (hp : dualCutCurrent (vertexPast ω hT hOne v) p ≠ 0) :
    let d := dualBaseInv (edgeEquiv.symm (outgoingEdge ω hT hOne v))
    (baseEdge p).val ∈ (BarlowMasson.treePath (dualField ω) hDual
      (d.1 + unit d.2) d.1).edges ∨
      baseEdge p = crossingDualEdge (outgoingEdge ω hT hOne v) := by
  let A := vertexPast ω hT hOne v
  let d := dualBaseInv (edgeEquiv.symm (outgoingEdge ω hT hOne v))
  let S : Set (Site 2 × Site 2) := {r | latticeCutFlux A r.1 r.2 ≠ 0}
  have hS : S.Finite := latticeCutFlux_finite_support A (vertexPast_finite ω hT hOne v)
  let F : Set (Site 2) := Prod.fst '' S ∪ Prod.snd '' S
  have hF : F.Finite := (hS.image Prod.fst).union (hS.image Prod.snd)
  let W := hF.toFinset
  have hW : ∀ x y, latticeCutFlux A x y ≠ 0 → x ∈ W ∧ y ∈ W := by
    intro x y hxy
    exact ⟨hF.mem_toFinset.mpr (Or.inl ⟨(x, y), hxy, rfl⟩),
      hF.mem_toFinset.mpr (Or.inr ⟨(x, y), hxy, rfl⟩)⟩
  have hsupport : ∀ x y, latticeCutFlux A x y ≠ 0 →
      (toGraph (dualField ω)).Adj x y ∨ s(x, y) = s(d.1 + unit d.2, d.1) := by
    intro x y hxy
    obtain ⟨q, hq, hdir⟩ := latticeCutFlux_ne_zero_edge A x y hxy
    by_cases heq : baseEdge (dualBase q) = outgoingEdge ω hT hOne v
    · have hname : dualBase q = edgeEquiv.symm (outgoingEdge ω hT hOne v) := by
        calc
          dualBase q = edgeEquiv.symm (baseEdge (dualBase q)) :=
            (edgeEquiv.symm_apply_apply _).symm
          _ = edgeEquiv.symm (outgoingEdge ω hT hOne v) := congrArg edgeEquiv.symm heq
      have hqd : q = d := by dsimp [d]; rw [← hname, dualBase_left_inv]
      right
      rcases hdir with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hqd]; exact Sym2.eq_swap
      · rw [hqd]
    · have hs := crossing_dual_selected ω hT hOne v (dualBase q)
        ((dualCutCurrent_ne_zero_iff A q).mp hq) heq
      rw [dualBase_left_inv] at hs
      have hadj : (toGraph (dualField ω)).Adj q.1 (q.1 + unit q.2) :=
        ⟨⟨q.2, Or.inl rfl⟩, hs⟩
      left
      rcases hdir with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hadj
      · exact hadj.symm
  have hflux : latticeCutFlux A p.1 (p.1 + unit p.2) ≠ 0 := by
    rwa [latticeCutFlux_base]
  have h := FiniteCirculation.support_mem_path_or_exception (toGraph (dualField ω)) hDual
    (d.1 + unit d.2) d.1 W (latticeCutFlux A) (latticeCutFlux_antisymmetric A)
    hW (fun x _ => latticeCutFlux_divergence_zero A W hW x) hsupport
    p.1 (p.1 + unit p.2) hflux
  rcases h with h | h
  · exact Or.inl h
  · right
    have hbase : baseEdge p = baseEdge d := Subtype.ext (h.trans Sym2.eq_swap)
    rw [hbase]
    dsimp [d]
    rw [← crossingDualEdge_baseEdge]
    exact congrArg crossingDualEdge (edgeEquiv.apply_symm_apply _)

/-- Both endpoints of every crossed original boundary edge belong to the genuine
selected dual-tree path. This includes the outgoing exception via the path endpoints. -/
theorem vertexPast_boundary_endpoints_mem_selected_path (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (hDual : IsTree (dualField ω)) (v : Site 2)
    (r : Site 2 × Fin 2)
    (hc : ((r.1 ∈ vertexPast ω hT hOne v ∧ r.1 + unit r.2 ∉ vertexPast ω hT hOne v) ∨
      (r.1 ∉ vertexPast ω hT hOne v ∧ r.1 + unit r.2 ∈ vertexPast ω hT hOne v))) :
    let d := dualBaseInv (edgeEquiv.symm (outgoingEdge ω hT hOne v))
    ∀ w ∈ ({(dualBaseInv r).1, (dualBaseInv r).1 + unit (dualBaseInv r).2} : Set (Site 2)),
      w ∈ (BarlowMasson.treePath (dualField ω) hDual (d.1 + unit d.2) d.1).support := by
  let p := dualBaseInv r
  let d := dualBaseInv (edgeEquiv.symm (outgoingEdge ω hT hOne v))
  let q := BarlowMasson.treePath (dualField ω) hDual (d.1 + unit d.2) d.1
  have hp : dualCutCurrent (vertexPast ω hT hOne v) p ≠ 0 := by
    apply (dualCutCurrent_ne_zero_iff _ p).mpr
    simpa only [p, dualBase_right_inv] using hc
  have h := vertexPast_dual_boundary_mem_path_or_outgoing ω hT hOne hDual v p hp
  change ∀ w ∈ ({p.1, p.1 + unit p.2} : Set (Site 2)), w ∈ q.support
  intro w hw
  rcases h with hpath | hout
  · rcases Set.mem_insert_iff.mp hw with hleft | hright
    · rw [hleft]
      exact Walk.fst_mem_support_of_mem_edges q hpath
    · rw [Set.mem_singleton_iff.mp hright]
      exact Walk.snd_mem_support_of_mem_edges q hpath
  · have hnamed : baseEdge p = baseEdge d := by
      rw [hout]
      dsimp [d]
      rw [← crossingDualEdge_baseEdge]
      exact congrArg crossingDualEdge (edgeEquiv.apply_symm_apply _).symm
    have hpd : p = d := baseEdge_injective hnamed
    change w ∈ ({p.1, p.1 + unit p.2} : Set (Site 2)) at hw
    rw [hpd] at hw
    rcases Set.mem_insert_iff.mp hw with hleft | hright
    · rw [hleft]
      exact q.end_mem_support
    · rw [Set.mem_singleton_iff.mp hright]
      exact q.start_mem_support

end
end FiniteAvalanches.Trees.Lattice.PastTail
