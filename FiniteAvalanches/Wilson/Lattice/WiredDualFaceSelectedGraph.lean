import FiniteAvalanches.Wilson.Lattice.WiredLimitDualDetourBox
import FiniteAvalanches.Sandpile.Burning.SpanningTree

/-! The selected dual lattice graph restricted to the finite face square. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

local instance decEqWiredEdgeDualFaceSelectedGraph (B : ℕ) :
    DecidableEq (FiniteWired.Edge B) := Classical.decEq _

/-- Original copies whose crossing dual lattice edge is selected. -/
def wiredDualFaceSelectedCopies (B : ℕ) (ω : EdgeField) : Finset (FiniteWired.Edge B) :=
  Finset.univ.filter (fun q => dualField ω (wiredCopyDualEdge q) = true)

/-- Selected face-copy adjacency is exactly selected dual lattice adjacency
between the corresponding face labels. -/
theorem wiredDualFaceSelectedCopies_adjacent_iff (B : ℕ) (ω : EdgeField)
    (v w : WiredDualFace B) :
    (wiredDualFaceGraph B).adjacent (wiredDualFaceSelectedCopies B ω) v w ↔
      (toGraph (dualField ω)).Adj (wiredDualFaceSite v) (wiredDualFaceSite w) := by
  constructor
  · rintro ⟨q, hq, hends⟩
    have hval : dualField ω (wiredCopyDualEdge q) = true := (Finset.mem_filter.mp hq).2
    have hmem := (edge_mem_toGraph_iff (dualField ω) (wiredCopyDualEdge q)).mpr hval
    change s(wiredDualFaceSite v, wiredDualFaceSite w) ∈ (toGraph (dualField ω)).edgeSet
    rw [← wiredDualFaceGraph_edge] at hmem
    rcases hends with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · simpa only [hl, hr] using hmem
    · simpa only [hl, hr, Sym2.eq_swap] using hmem
  · intro hadj
    have hlattice : (lattice 2).Adj (wiredDualFaceSite v) (wiredDualFaceSite w) :=
      toGraph_le_lattice (dualField ω) hadj
    obtain ⟨q, _, hends⟩ := (wiredDualFaceGraph_adjacent_iff B v w).mpr hlattice
    let e : LatticeEdge := ⟨s(wiredDualFaceSite v, wiredDualFaceSite w), hlattice⟩
    have he : wiredCopyDualEdge q = e := by
      apply Subtype.ext
      rw [← wiredDualFaceGraph_edge]
      change s(wiredDualFaceSite ((wiredDualFaceGraph B).left q),
        wiredDualFaceSite ((wiredDualFaceGraph B).right q)) =
          s(wiredDualFaceSite v, wiredDualFaceSite w)
      rcases hends with ⟨hl, hr⟩ | ⟨hr, hl⟩
      · simp only [hl, hr]
      · simpa only [hl, hr] using (Sym2.eq_swap :
          s(wiredDualFaceSite w, wiredDualFaceSite v) = s(wiredDualFaceSite v, wiredDualFaceSite w))
    have hval : dualField ω (wiredCopyDualEdge q) = true := by
      rw [he]
      exact (edge_mem_toGraph_iff (dualField ω) e).mp hadj
    exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hval⟩, hends⟩

/-- A selected dual walk confined to the face square lifts to a walk using the
same selected original face copies. -/
theorem wiredDualFaceSelectedCopies_reaches_of_walk (B : ℕ) (ω : EdgeField)
    {u v : Site 2} (p : (toGraph (dualField ω)).Walk u v)
    (hbox : ∀ z ∈ p.support, inDualFaceBox B z) :
    (wiredDualFaceGraph B).reaches (wiredDualFaceSelectedCopies B ω)
      (wiredDualFaceOfSite B u (hbox u p.start_mem_support))
      (wiredDualFaceOfSite B v (hbox v p.end_mem_support)) := by
  induction p with
  | nil => exact Relation.ReflTransGen.refl
  | @cons u v w huv p ih =>
    have htail : ∀ z ∈ p.support, inDualFaceBox B z := by
      intro z hz
      apply hbox z
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
      exact Or.inr hz
    have hstep : (wiredDualFaceGraph B).adjacent (wiredDualFaceSelectedCopies B ω)
        (wiredDualFaceOfSite B u (hbox u (by simp [SimpleGraph.Walk.support_cons])))
        (wiredDualFaceOfSite B v (htail v p.start_mem_support)) := by
      apply (wiredDualFaceSelectedCopies_adjacent_iff B ω _ _).mpr
      exact huv
    exact (Relation.ReflTransGen.single hstep).trans (ih htail)

/-- A finite selected dual detour lifts to the selected face-copy graph in all
sufficiently large wired boxes. -/
theorem dualDetour_eventually_reaches_in_selectedFaceGraph (ω : EdgeField) (d : LatticeEdge)
    (p : (toGraph (dualField ω)).Walk d.val.out.1 d.val.out.2) :
    ∀ᶠ B : ℕ in atTop, ∃ hu : inDualFaceBox B d.val.out.1, ∃ hv : inDualFaceBox B d.val.out.2,
      (wiredDualFaceGraph B).reaches (wiredDualFaceSelectedCopies B ω)
        (wiredDualFaceOfSite B d.val.out.1 hu) (wiredDualFaceOfSite B d.val.out.2 hv) := by
  have hsites : ∀ᶠ B : ℕ in atTop, ∀ z : {z // z ∈ p.support}, FiniteWired.inBox B z.val :=
    eventually_all.mpr (fun z => eventually_finiteWired_inBox z.val)
  filter_upwards [hsites] with B hB
  have hbox : ∀ z ∈ p.support, inDualFaceBox B z := by
    intro z hz
    exact inDualFaceBox_of_inBox B z (hB ⟨z, hz⟩)
  exact ⟨hbox _ p.start_mem_support, hbox _ p.end_mem_support,
    wiredDualFaceSelectedCopies_reaches_of_walk B ω p hbox⟩

/-- If the infinite dual field is a forest, its selected copies form a forest
inside every finite face square. -/
theorem wiredDualFaceSelectedCopies_is_forest (B : ℕ) (ω : EdgeField)
    (hacyclic : (toGraph (dualField ω)).IsAcyclic) :
    (wiredDualFaceGraph B).is_forest (wiredDualFaceSelectedCopies B ω) := by
  let G := wiredDualFaceGraph B
  let F := wiredDualFaceSelectedCopies B ω
  let f : G.toSimple F →g toGraph (dualField ω) :=
    ⟨wiredDualFaceSite, fun h => (wiredDualFaceSelectedCopies_adjacent_iff B ω _ _).mp h⟩
  have hs : (G.toSimple F).IsAcyclic := hacyclic.comap f (wiredDualFaceSite_injective B)
  have hi : Set.InjOn G.edge (F : Set (FiniteWired.Edge B)) := by
    intro e he g hg heq
    apply wiredDualFaceGraph_endpointPair_injective B
    exact heq
  exact FiniteAvalanches.Sandpile.Burning.copied_forest_of_simple G F hs hi

end
end FiniteAvalanches.Wilson.Lattice
