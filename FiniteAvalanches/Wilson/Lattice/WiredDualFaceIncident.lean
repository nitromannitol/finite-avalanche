import FiniteAvalanches.Wilson.Lattice.WiredDualFaceInnerBox
import FiniteAvalanches.Wilson.Lattice.FreeInteriorCopies

/-! Incident-edge comparison inside the dual face square. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- A centered-box incident copy remains incident after inclusion in the face square. -/
def wiredDualFaceInnerIncident (B : ℕ) (x : FiniteWired.Active B)
    (e : IncidentCopy (freeBoxGraph B) x) :
    IncidentCopy (wiredDualFaceGraph B) (wiredDualFaceInnerVertex B x) :=
  ⟨wiredDualFaceInnerCopy B e.val, by
    have hx : wiredDualFaceInnerVertex B x ∈
        s(wiredDualFaceInnerVertex B ((freeBoxGraph B).left e.val),
          wiredDualFaceInnerVertex B ((freeBoxGraph B).right e.val)) := by
      rcases e.property with h | h
      · exact Sym2.mem_iff.mpr (Or.inl (congrArg (wiredDualFaceInnerVertex B) h).symm)
      · exact Sym2.mem_iff.mpr (Or.inr (congrArg (wiredDualFaceInnerVertex B) h).symm)
    rw [← wiredDualFaceInnerCopy_endpoints] at hx
    exact (Sym2.mem_iff.mp hx).elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩

/-- Inclusion of centered-box incident copies is injective. -/
theorem wiredDualFaceInnerIncident_injective (B : ℕ) (x : FiniteWired.Active B) :
    Function.Injective (wiredDualFaceInnerIncident B x) := by
  intro e f h
  apply Subtype.ext
  exact wiredDualFaceInnerCopy_injective B (congrArg Subtype.val h)

/-- Every neighbor of a site in a centered box lies in the next larger box. -/
theorem inBox_succ_of_adjacent (B : ℕ) (x y : Site 2) (hx : FiniteWired.inBox B x)
    (hxy : (lattice 2).Adj x y) : FiniteWired.inBox (B + 1) y := by
  obtain ⟨i, hi | hi⟩ := hxy
  · rw [hi]
    simpa only [FiniteWired.step, if_true] using inBox_succ_of_step B x hx (i, true)
  · have hy : y = x + FiniteWired.step (i, false) := by
      simp only [FiniteWired.step, Bool.false_eq_true, if_false]
      rw [hi]
      abel
    rw [hy]
    exact inBox_succ_of_step B x hx (i, false)

/-- At vertices one step from the centered box boundary, all incident face
copies come from the centered box. -/
theorem wiredDualFaceInnerIncident_surjective (B : ℕ) (x : FiniteWired.Active (B + 1))
    (hx : FiniteWired.inBox B (FiniteWired.site x)) :
    Function.Surjective (wiredDualFaceInnerIncident (B + 1) x) := by
  intro e
  let v := wiredDualFaceInnerVertex (B + 1) x
  have hL : (wiredDualFaceGraph (B + 1)).left e.val = v ∨
      (wiredDualFaceGraph (B + 1)).right e.val = v := e.property
  have hadj : (lattice 2).Adj
      (wiredDualFaceSite ((wiredDualFaceGraph (B + 1)).left e.val))
      (wiredDualFaceSite ((wiredDualFaceGraph (B + 1)).right e.val)) := by
    apply (wiredDualFaceGraph_adjacent_iff (B + 1) _ _).mp
    exact ⟨e.val, Finset.mem_univ _, Or.inl ⟨rfl, rfl⟩⟩
  have hv : FiniteWired.inBox (B + 1) (wiredDualFaceSite v) := fun i => (x i).property
  have hends : FiniteWired.inBox (B + 1)
        (wiredDualFaceSite ((wiredDualFaceGraph (B + 1)).left e.val)) ∧
      FiniteWired.inBox (B + 1)
        (wiredDualFaceSite ((wiredDualFaceGraph (B + 1)).right e.val)) := by
    rcases hL with hL | hR
    · refine ⟨hL ▸ hv, ?_⟩
      apply inBox_succ_of_adjacent B (FiniteWired.site x) _ hx
      simpa only [hL, wiredDualFaceSite_innerVertex, v] using hadj
    · refine ⟨?_, hR ▸ hv⟩
      apply inBox_succ_of_adjacent B (FiniteWired.site x) _ hx
      simpa only [hR, wiredDualFaceSite_innerVertex, v] using hadj.symm
  have hbox : ∀ z ∈ (wiredCopyDualEdge e.val).val, FiniteWired.inBox (B + 1) z := by
    intro z hz
    rw [← wiredDualFaceGraph_edge] at hz
    rcases Sym2.mem_iff.mp hz with rfl | rfl
    · exact hends.1
    · exact hends.2
  obtain ⟨q, hq⟩ := (wiredDualFaceInnerCopy_range_iff (B + 1) e.val).mpr hbox
  have hqinc : (freeBoxGraph (B + 1)).left q = x ∨
      (freeBoxGraph (B + 1)).right q = x := by
    have hmem : v ∈ s(wiredDualFaceInnerVertex (B + 1) ((freeBoxGraph (B + 1)).left q),
        wiredDualFaceInnerVertex (B + 1) ((freeBoxGraph (B + 1)).right q)) := by
      rw [← wiredDualFaceInnerCopy_endpoints, hq]
      exact Sym2.mem_iff.mpr (hL.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm))
    rcases Sym2.mem_iff.mp hmem with h | h
    · exact Or.inl ((wiredDualFaceInnerVertex_injective (B + 1) h).symm)
    · exact Or.inr ((wiredDualFaceInnerVertex_injective (B + 1) h).symm)
  refine ⟨⟨q, hqinc⟩, ?_⟩
  exact Subtype.ext hq

/-- The incident-copy inclusion preserves the other endpoint. -/
theorem wiredDualFaceInnerIncident_head (B : ℕ) (x : FiniteWired.Active B)
    (e : IncidentCopy (freeBoxGraph B) x) :
    incidentCopyHead (wiredDualFaceGraph B) (wiredDualFaceInnerVertex B x)
        (wiredDualFaceInnerIncident B x e) =
      wiredDualFaceInnerVertex B (incidentCopyHead (freeBoxGraph B) x e) := by
  have hf : s(x, incidentCopyHead (freeBoxGraph B) x e) =
      s((freeBoxGraph B).left e.val, (freeBoxGraph B).right e.val) := by
    rcases incidentCopy_endpoints (freeBoxGraph B) x e with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · rw [hl, hr]
    · rw [hl, hr]
      exact Sym2.eq_swap
  have hd : s(wiredDualFaceInnerVertex B x,
        incidentCopyHead (wiredDualFaceGraph B) (wiredDualFaceInnerVertex B x)
          (wiredDualFaceInnerIncident B x e)) =
      s((wiredDualFaceGraph B).left (wiredDualFaceInnerCopy B e.val),
        (wiredDualFaceGraph B).right (wiredDualFaceInnerCopy B e.val)) := by
    rcases incidentCopy_endpoints (wiredDualFaceGraph B) (wiredDualFaceInnerVertex B x)
      (wiredDualFaceInnerIncident B x e) with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · change (wiredDualFaceGraph B).left (wiredDualFaceInnerCopy B e.val) = _ at hl
      change (wiredDualFaceGraph B).right (wiredDualFaceInnerCopy B e.val) = _ at hr
      rw [hl, hr]
    · change (wiredDualFaceGraph B).right (wiredDualFaceInnerCopy B e.val) = _ at hr
      change (wiredDualFaceGraph B).left (wiredDualFaceInnerCopy B e.val) = _ at hl
      rw [hl, hr]
      exact Sym2.eq_swap
  rw [wiredDualFaceInnerCopy_endpoints] at hd
  have hm := congrArg (Sym2.map (wiredDualFaceInnerVertex B)) hf
  rw [Sym2.map_mk, Sym2.map_mk] at hm
  have hs := hd.trans hm.symm
  rcases Sym2.eq_iff.mp hs with h | h
  · exact h.2
  · exact h.2.trans h.1

/-- Interior centered-box and face-square incident copies are in bijection. -/
def wiredDualFaceInnerIncidentEquiv (B : ℕ) (x : FiniteWired.Active (B + 1))
    (hx : FiniteWired.inBox B (FiniteWired.site x)) :
    IncidentCopy (freeBoxGraph (B + 1)) x ≃
      IncidentCopy (wiredDualFaceGraph (B + 1)) (wiredDualFaceInnerVertex (B + 1) x) :=
  Equiv.ofBijective (wiredDualFaceInnerIncident (B + 1) x)
    ⟨wiredDualFaceInnerIncident_injective (B + 1) x,
      wiredDualFaceInnerIncident_surjective B x hx⟩

end
end FiniteAvalanches.Wilson.Lattice
