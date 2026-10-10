module

public import FiniteAvalanches.Trees.CopiedEdges
public import FiniteAvalanches.Trees.RootedPaths

@[expose] public section

/-! Rooted joining geometry on ordinary copied-edge spanning-tree subsets. -/
open scoped Classical
namespace FiniteAvalanches.Trees.Multigraph
open FiniteAvalanches.Trees.RootedPaths
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : Multigraph V E)

/-- Ordinary spanning trees are actual subsets of the original edge-copy carrier. -/
abbrev SpanningTree := G.ComponentTree Set.univ

/-- Descendants, including the vertex itself, defined by the unique actual rooted path. -/
def descendants (t : G.SpanningTree) (r a : V) : Set V :=
  {x | ancestor (G.toSimple_isTree t.property) r a x}

/-- The actual lowest common ancestor of a nonempty marked set in an ordinary tree. -/
noncomputable def ancestorOf (t : G.SpanningTree) (r : V) (S : Set V) (hS : S.Nonempty) : V :=
  commonAncestor (G.toSimple_isTree t.property) r S hS

/-- The actual connecting subtree, independent of the root. -/
def span (t : G.SpanningTree) (S : Set V) : Set V :=
  connectingSubtree (G.toSimple_isTree t.property) S

theorem walk_reaches_erase_of_not_mem {t : Finset E} {e : E} {a x y : V}
    (hae : G.left e = a ∨ G.right e = a) (p : (G.toSimple t).Walk x y)
    (ha : a ∉ p.support) : G.reaches (t.erase e) x y := by
  induction p with
  | nil => exact .refl
  | @cons x z y hxz q ih =>
    have haq : a ∉ q.support := fun h => ha (List.mem_cons_of_mem _ h)
    have hax : a ≠ x := fun h => ha (h ▸ List.mem_cons_self)
    have haz : a ≠ z := fun h => haq (h ▸ q.start_mem_support)
    apply Relation.ReflTransGen.head _ (ih haq)
    rcases hxz with ⟨f, hf, h | h⟩
    · refine ⟨f, Finset.mem_erase.mpr ⟨?_, hf⟩, Or.inl h⟩
      intro hfe
      subst f
      rcases hae with hae | hae
      · exact hax (hae.symm.trans h.1)
      · exact haz (hae.symm.trans h.2)
    · refine ⟨f, Finset.mem_erase.mpr ⟨?_, hf⟩, Or.inr h⟩
      intro hfe
      subst f
      rcases hae with hae | hae
      · exact haz (hae.symm.trans h.2)
      · exact hax (hae.symm.trans h.1)

omit [DecidableEq E] in
theorem walk_mem_side {C : Set V} {t : Finset E}
    (ht : ∀ e ∈ t, G.left e ∈ C ↔ G.right e ∈ C)
    {x y : V} (p : (G.toSimple t).Walk x y) (hx : x ∈ C) :
    ∀ z ∈ p.support, z ∈ C := by
  induction p with
  | nil => intro z hz; simpa using (List.mem_singleton.mp hz) ▸ hx
  | @cons x v y h q ih =>
    have hv : v ∈ C := (G.reaches_mem_iff ht (Relation.ReflTransGen.single h)).mp hx
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hx
    · exact ih hv z hz

/-- On a cut tree, the inside endpoint's descendants are exactly the cut component. -/
theorem descendants_eq_cut {C : Set V} (p : G.CutTree C) (r v : V)
    (hr : r ∉ C) (hv : v ∈ C)
    (hve : G.left p.val.2 = v ∨ G.right p.val.2 = v) :
    G.descendants ⟨p.val.1, p.property.1⟩ r v = C := by
  let t : G.SpanningTree := ⟨p.val.1, p.property.1⟩
  let hT := G.toSimple_isTree p.property.1
  ext x
  change ancestor hT r v x ↔ x ∈ C
  constructor
  · intro h
    by_contra hx
    have hd : G.reaches (p.val.1.erase p.val.2) r x := p.property.2.2.2.2.2 r hr x hx
    obtain ⟨q⟩ := (G.toSimple_reachable _ r x).mpr hd
    have hle : G.toSimple (p.val.1.erase p.val.2) ≤ G.toSimple p.val.1 := by
      intro a b hab
      rcases hab with ⟨e, he, h⟩
      exact ⟨e, Finset.mem_of_mem_erase he, h⟩
    let q' : (G.toSimple p.val.1).Walk r x := q.mapLe hle
    have hqp : path hT r x = q'.toPath.val := path_eq hT _ q'.toPath.property
    unfold ancestor at h
    rw [hqp] at h
    have hqv : v ∈ q'.support := q'.support_toPath_subset_support h
    have hqv' : v ∈ q.support := by
      change v ∈ (q.mapLe hle).support at hqv
      rwa [SimpleGraph.Walk.support_mapLe_eq_support] at hqv
    have hside := G.walk_mem_side (C := Cᶜ) (fun e he => not_congr (p.property.2.2.2.1 e he)) q hr v hqv'
    exact hside hv
  · intro hx
    by_contra hnot
    have hreach := G.walk_reaches_erase_of_not_mem hve (path hT r x) hnot
    have hsame := G.reaches_mem_iff p.property.2.2.2.1 hreach
    exact hr (hsame.mpr hx)

/-- The common-ancestor descendant set equals the cut support exactly for joins at the
actual minimal connecting subtree. This is the missing joining geometry. -/
theorem ancestor_descendants_eq_cut_iff {C S : Set V} (p : G.CutTree C)
    (r v : V) (hr : r ∉ C) (hv : v ∈ C) (hSC : S ⊆ C) (hS : S.Nonempty)
    (hve : G.left p.val.2 = v ∨ G.right p.val.2 = v) :
    G.descendants ⟨p.val.1, p.property.1⟩ r
        (G.ancestorOf ⟨p.val.1, p.property.1⟩ r S hS) = C ↔
      v ∈ G.span ⟨p.val.1, p.property.1⟩ S := by
  let t : G.SpanningTree := ⟨p.val.1, p.property.1⟩
  let hT := G.toSimple_isTree p.property.1
  have hvdesc := G.descendants_eq_cut p r v hr hv hve
  have hvcommon : ∀ x ∈ S, ancestor hT r v x := by
    intro x hx
    change x ∈ G.descendants t r v
    rw [hvdesc]
    exact hSC hx
  have hca := commonAncestor_spec hT r S hS
  have heq : G.descendants t r (G.ancestorOf t r S hS) = C ↔
      G.ancestorOf t r S hS = v := by
    constructor
    · intro h
      have hav : ancestor hT r (commonAncestor hT r S hS) v := by
        change v ∈ G.descendants t r (G.ancestorOf t r S hS)
        rw [h]
        exact hv
      exact ancestor_antisymm hT hav (hca.2 v hvcommon)
    · intro h
      rw [h]
      exact hvdesc
  exact heq.trans (commonAncestor_eq_iff_mem_connectingSubtree hT r S hS hvcommon)

end FiniteAvalanches.Trees.Multigraph
