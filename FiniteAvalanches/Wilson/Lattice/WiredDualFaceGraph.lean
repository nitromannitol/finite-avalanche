import FiniteAvalanches.Wilson.Lattice.WiredDualFaceEdges
import FiniteAvalanches.Trees.Joining

/-! The finite dual face graph, retaining the original wired copy carrier. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- Face vertices of the dual square, labeled by lattice sites. -/
abbrev WiredDualFace (B : ℕ) := Fin 2 → Set.Icc (-(B : ℤ) - 1) (B : ℤ)

/-- The lattice-site label of a face vertex. -/
def wiredDualFaceSite {B : ℕ} (v : WiredDualFace B) : Site 2 := fun i => (v i).val

/-- A site in the dual face square determines its unique face vertex. -/
def wiredDualFaceOfSite (B : ℕ) (z : Site 2) (hz : inDualFaceBox B z) : WiredDualFace B :=
  fun i => ⟨z i, hz i⟩

/-- Site labels of represented face vertices are unchanged. -/
theorem wiredDualFaceSite_ofSite (B : ℕ) (z : Site 2) (hz : inDualFaceBox B z) :
    wiredDualFaceSite (wiredDualFaceOfSite B z hz) = z := rfl

/-- Distinct face vertices have distinct lattice-site labels. -/
theorem wiredDualFaceSite_injective (B : ℕ) : Function.Injective (@wiredDualFaceSite B) := by
  intro v w h
  funext i
  exact Subtype.ext (congrFun h i)

/-- The first dual endpoint of a wired original copy. -/
def wiredDualFaceLeft {B : ℕ} (e : FiniteWired.Edge B) : WiredDualFace B :=
  wiredDualFaceOfSite B (wiredCopyDualEdge e).val.out.1
    (wiredCopyDualEdge_endpoints_inDualFaceBox B e _ (Sym2.out_fst_mem _))

/-- The second dual endpoint of a wired original copy. -/
def wiredDualFaceRight {B : ℕ} (e : FiniteWired.Edge B) : WiredDualFace B :=
  wiredDualFaceOfSite B (wiredCopyDualEdge e).val.out.2
    (wiredCopyDualEdge_endpoints_inDualFaceBox B e _ (Sym2.out_snd_mem _))

/-- The face endpoints recover the actual crossing lattice edge. -/
theorem wiredDualFace_endpoints {B : ℕ} (e : FiniteWired.Edge B) :
    s(wiredDualFaceSite (wiredDualFaceLeft e), wiredDualFaceSite (wiredDualFaceRight e)) =
      (wiredCopyDualEdge e).val := by
  change s((wiredCopyDualEdge e).val.out.1, (wiredCopyDualEdge e).val.out.2) = _
  exact (wiredCopyDualEdge e).val.out_eq

/-- A crossing dual edge joins two different face vertices. -/
theorem wiredDualFace_endpoints_ne {B : ℕ} (e : FiniteWired.Edge B) :
    wiredDualFaceLeft e ≠ wiredDualFaceRight e := by
  intro he
  have hs := congrArg wiredDualFaceSite he
  have ha : (lattice 2).Adj (wiredDualFaceSite (wiredDualFaceLeft e))
      (wiredDualFaceSite (wiredDualFaceRight e)) := by
    change s(wiredDualFaceSite (wiredDualFaceLeft e), wiredDualFaceSite (wiredDualFaceRight e)) ∈
      (lattice 2).edgeSet
    rw [wiredDualFace_endpoints]
    exact (wiredCopyDualEdge e).property
  exact (lattice 2).loopless.irrefl _ (hs ▸ ha)

/-- The dual face multigraph uses exactly the original wired edge copies. -/
def wiredDualFaceGraph (B : ℕ) : Multigraph (WiredDualFace B) (FiniteWired.Edge B) :=
  Multigraph.ofEndpoints (fun e => (wiredDualFaceLeft e, wiredDualFaceRight e))
    (fun e => wiredDualFace_endpoints_ne e)

/-- The dual endpoints of any copy are precisely its crossing lattice edge. -/
theorem wiredDualFaceGraph_edge (B : ℕ) (e : FiniteWired.Edge B) :
    s(wiredDualFaceSite ((wiredDualFaceGraph B).left e),
      wiredDualFaceSite ((wiredDualFaceGraph B).right e)) = (wiredCopyDualEdge e).val :=
  wiredDualFace_endpoints e

/-- Distinct dual graph copies have distinct endpoint pairs. -/
theorem wiredDualFaceGraph_endpointPair_injective (B : ℕ) :
    Function.Injective (fun e : FiniteWired.Edge B =>
      s((wiredDualFaceGraph B).left e, (wiredDualFaceGraph B).right e)) := by
  intro e f h
  apply wiredCopyDualEdge_injective B
  apply Subtype.ext
  have hm := congrArg (Sym2.map (wiredDualFaceSite : WiredDualFace B → Site 2)) h
  simpa only [Sym2.map_mk, wiredDualFaceGraph_edge] using hm

/-- The face graph has exactly the square-lattice adjacencies between its vertices. -/
theorem wiredDualFaceGraph_adjacent_iff (B : ℕ) (v w : WiredDualFace B) :
    (wiredDualFaceGraph B).adjacent Finset.univ v w ↔
      (lattice 2).Adj (wiredDualFaceSite v) (wiredDualFaceSite w) := by
  constructor
  · rintro ⟨e, _, hends⟩
    have ha : (lattice 2).Adj (wiredDualFaceSite ((wiredDualFaceGraph B).left e))
        (wiredDualFaceSite ((wiredDualFaceGraph B).right e)) := by
      change s(wiredDualFaceSite ((wiredDualFaceGraph B).left e),
        wiredDualFaceSite ((wiredDualFaceGraph B).right e)) ∈ (lattice 2).edgeSet
      rw [wiredDualFaceGraph_edge]
      exact (wiredCopyDualEdge e).property
    rcases hends with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · simpa only [hl, hr] using ha
    · simpa only [hl, hr] using ha.symm
  · intro h
    let e : LatticeEdge := ⟨s(wiredDualFaceSite v, wiredDualFaceSite w), h⟩
    have hv : inDualFaceBox B (wiredDualFaceSite v) := fun i => (v i).property
    have hw : inDualFaceBox B (wiredDualFaceSite w) := fun i => (w i).property
    have hebox : ∀ z ∈ e.val, inDualFaceBox B z := by
      intro z hz
      rcases Sym2.mem_iff.mp hz with rfl | rfl
      · exact hv
      · exact hw
    obtain ⟨q, hq⟩ := (dualFaceEdge_iff_wiredCopy B e).mp hebox
    have hp : s((wiredDualFaceGraph B).left q, (wiredDualFaceGraph B).right q) = s(v, w) := by
      apply (Sym2.map.injective (wiredDualFaceSite_injective B))
      rw [Sym2.map_mk, wiredDualFaceGraph_edge, Sym2.map_mk]
      exact congrArg Subtype.val hq
    rcases Sym2.eq_iff.mp hp with hp | hp
    · exact ⟨q, Finset.mem_univ _, Or.inl hp⟩
    · exact ⟨q, Finset.mem_univ _, Or.inr ⟨hp.2, hp.1⟩⟩

end
end FiniteAvalanches.Wilson.Lattice
