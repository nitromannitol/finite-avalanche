import FiniteAvalanches.Trees.Lattice.WiredOriginalFieldV1
import FiniteAvalanches.Trees.CopiedEdges

/-! The candidate inside-tree carrier in incoming main.tex177, in original coordinates. -/

set_option autoImplicit false

namespace FiniteAvalanches.Trees.Lattice.CurrentInsideRawTree

open LatticeProb FiniteAvalanches.Sandpile TreeMeasurability11 CurrentOriginalField
open scoped Classical
noncomputable section

/-- The literal graph selected by the same candidate copied-edge image. -/
def rawGraph {N : ℕ} (H : Finset (FiniteWired.Edge N)) : SimpleGraph (Site 2) :=
  toGraph (fun f : LatticeEdge => decide (f ∈ H.image originalCopyEdge))

/-- The literal lift of an original support vertex to its active finite vertex. -/
def rawVertexLift (N : ℕ) (F : Finset (Site 2))
    (hbox : ∀ x ∈ F, FiniteWired.inBox N x) :
    ↥(F : Set (Site 2)) → activeLift N (F : Set (Site 2)) :=
  fun x => ⟨some (FiniteWired.activeOfSite N x.val (hbox x.val x.property)),
    ⟨FiniteWired.activeOfSite N x.val (hbox x.val x.property), rfl, x.property⟩⟩

theorem rawVertexLift_bijective (N : ℕ) (F : Finset (Site 2))
    (hbox : ∀ x ∈ F, FiniteWired.inBox N x) :
    Function.Bijective (rawVertexLift N F hbox) := by
  constructor
  · intro x y h
    apply Subtype.ext
    have hs := Option.some.inj (congrArg Subtype.val h)
    exact congrArg FiniteWired.site hs
  · intro v
    obtain ⟨a, hv, ha⟩ := v.property
    refine ⟨⟨FiniteWired.site a, ha⟩, Subtype.ext ?_⟩
    change some (FiniteWired.activeOfSite N (FiniteWired.site a) _) = v.val
    rw [hv]
    apply congrArg some
    exact FiniteWired.site_injective N rfl

/-- This equivalence is constructed from the proved literal lift bijection. -/
def rawVertexEquiv (N : ℕ) (F : Finset (Site 2))
    (hbox : ∀ x ∈ F, FiniteWired.inBox N x) :
    (F : Set (Site 2)) ≃ activeLift N (F : Set (Site 2)) :=
  Equiv.ofBijective (rawVertexLift N F hbox) (rawVertexLift_bijective N F hbox)

theorem rawVertexLift_site (N : ℕ) (F : Finset (Site 2))
    (hbox : ∀ x ∈ F, FiniteWired.inBox N x) (a : FiniteWired.Active N)
    (ha : FiniteWired.site a ∈ F) :
    (rawVertexLift N F hbox ⟨FiniteWired.site a, ha⟩).val = some a := by
  apply congrArg some
  exact FiniteWired.site_injective N rfl

/-- Both raw endpoints belong to F exactly when the copied subset is supported in its lift.
The reverse implication rules out all exit copies using their actual outside endpoint. -/
theorem supported_iff_raw_endpoints (N : ℕ) (F : Finset (Site 2))
    (hbox : ∀ x ∈ F, FiniteWired.inBox N x) (H : Finset (FiniteWired.Edge N)) :
    (WiredTrees.graph N).supported (activeLift N (F : Set (Site 2))) H ↔
      ∀ f ∈ H.image originalCopyEdge, ∃ u ∈ F, ∃ v ∈ F, f.val = s(u, v) := by
  constructor
  · intro hs f hf
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hf
    have h := hs e he
    cases e with
    | inl i =>
      change some i.val.1 ∈ activeLift N (F : Set (Site 2)) ∧
        some i.val.2 ∈ activeLift N (F : Set (Site 2)) at h
      rw [some_mem_activeLift, some_mem_activeLift] at h
      exact ⟨FiniteWired.site i.val.1, h.1, FiniteWired.site i.val.2, h.2, rfl⟩
    | inr i =>
      exact False.elim (sink_not_mem_activeLift N (F : Set (Site 2)) h.2)
  · intro hs e he
    obtain ⟨u, hu, v, hv, hraw⟩ := hs (originalCopyEdge e)
      (Finset.mem_image_of_mem originalCopyEdge he)
    cases e with
    | inl i =>
      change s(FiniteWired.site i.val.1, FiniteWired.site i.val.2) = s(u, v) at hraw
      change some i.val.1 ∈ activeLift N (F : Set (Site 2)) ∧
        some i.val.2 ∈ activeLift N (F : Set (Site 2))
      rw [some_mem_activeLift, some_mem_activeLift]
      rcases Sym2.eq_iff.mp hraw with h | h
      · rw [h.1, h.2]; exact ⟨hu, hv⟩
      · rw [h.1, h.2]; exact ⟨hv, hu⟩
    | inr i =>
      change s(FiniteWired.site i.val.1,
        FiniteWired.site i.val.1 + FiniteWired.step i.val.2) = s(u, v) at hraw
      rcases Sym2.eq_iff.mp hraw with h | h
      · exact False.elim (i.property (h.2.symm ▸ hbox v hv))
      · exact False.elim (i.property (h.2.symm ▸ hbox u hu))

/-- Copied adjacency on active vertices is the same literal raw adjacency. -/
theorem adjacency_iff_raw {N : ℕ} (F : Finset (Site 2))
    (H : Finset (FiniteWired.Edge N))
    (hs : (WiredTrees.graph N).supported (activeLift N (F : Set (Site 2))) H)
    (a b : FiniteWired.Active N) :
    (WiredTrees.graph N).adjacent H (some a) (some b) ↔
      (rawGraph H).Adj (FiniteWired.site a) (FiniteWired.site b) := by
  constructor
  · rintro ⟨e, he, h⟩
    cases e with
    | inl i =>
      change (some i.val.1 = some a ∧ some i.val.2 = some b) ∨
        (some i.val.2 = some a ∧ some i.val.1 = some b) at h
      rcases h with h | h
      · have ha := Option.some.inj h.1
        have hb := Option.some.inj h.2
        subst a; subst b
        refine ⟨(interiorEdge i).property, ?_⟩
        exact decide_eq_true (Finset.mem_image_of_mem originalCopyEdge he)
      · have ha := Option.some.inj h.1
        have hb := Option.some.inj h.2
        subst a; subst b
        refine ⟨(interiorEdge i).property.symm, ?_⟩
        apply decide_eq_true
        exact Finset.mem_image.mpr ⟨.inl i, he, Subtype.ext Sym2.eq_swap⟩
    | inr i => exact False.elim (sink_not_mem_activeLift N (F : Set (Site 2)) (hs _ he).2)
  · rintro ⟨hxy, hpres⟩
    have hmem := of_decide_eq_true hpres
    obtain ⟨e, he, hraw⟩ := Finset.mem_image.mp hmem
    cases e with
    | inl i =>
      have hpair := congrArg Subtype.val hraw
      rcases Sym2.eq_iff.mp hpair with h | h
      · exact ⟨.inl i, he, Or.inl ⟨congrArg some (FiniteWired.site_injective N h.1),
          congrArg some (FiniteWired.site_injective N h.2)⟩⟩
      · exact ⟨.inl i, he, Or.inr ⟨congrArg some (FiniteWired.site_injective N h.2),
          congrArg some (FiniteWired.site_injective N h.1)⟩⟩
    | inr i => exact False.elim (sink_not_mem_activeLift N (F : Set (Site 2)) (hs _ he).2)

/-- Supported copied paths remain in the complete lifted support. -/
theorem reaches_induced_iff {N : ℕ} (F : Finset (Site 2))
    (H : Finset (FiniteWired.Edge N))
    (hs : (WiredTrees.graph N).supported (activeLift N (F : Set (Site 2))) H)
    (x y : activeLift N (F : Set (Site 2))) :
    (WiredTrees.graph N).reaches H x.val y.val ↔
      (((WiredTrees.graph N).toSimple H).induce (activeLift N (F : Set (Site 2)))).Reachable x y := by
  constructor
  · intro hr
    have liftReach (a : FiniteWired.Vertex N) (ha : a ∈ activeLift N (F : Set (Site 2)))
        (b : FiniteWired.Vertex N) (hab : (WiredTrees.graph N).reaches H a b) :
        ∀ hb : b ∈ activeLift N (F : Set (Site 2)),
          (((WiredTrees.graph N).toSimple H).induce (activeLift N (F : Set (Site 2)))).Reachable
            ⟨a, ha⟩ ⟨b, hb⟩ := by
      induction hab with
      | refl => intro hb; exact SimpleGraph.Reachable.refl _
      | @tail b c _ hbc ih =>
        intro hc
        have hb : b ∈ activeLift N (F : Set (Site 2)) := by
          obtain ⟨e, he, h | h⟩ := hbc
          · exact h.1 ▸ (hs e he).1
          · exact h.1 ▸ (hs e he).2
        have hstep : (((WiredTrees.graph N).toSimple H).induce
            (activeLift N (F : Set (Site 2)))).Adj ⟨b, hb⟩ ⟨c, hc⟩ := hbc
        exact (ih hb).trans hstep.reachable
    exact liftReach x.val x.property y.val hr y.property
  · intro hr
    exact ((WiredTrees.graph N).toSimple_reachable H x.val y.val).mp
      (hr.map (SimpleGraph.Embedding.induce (activeLift N (F : Set (Site 2)))).toHom)


/-- The induced copied and raw graphs are isomorphic on every support vertex. -/
def insideGraphIso (N : ℕ) (F : Finset (Site 2))
    (hbox : ∀ x ∈ F, FiniteWired.inBox N x) (H : Finset (FiniteWired.Edge N))
    (hs : (WiredTrees.graph N).supported (activeLift N (F : Set (Site 2))) H) :
    (rawGraph H).induce (F : Set (Site 2)) ≃g
      ((WiredTrees.graph N).toSimple H).induce (activeLift N (F : Set (Site 2))) where
  toEquiv := rawVertexEquiv N F hbox
  map_rel_iff' := by
    intro x y
    exact adjacency_iff_raw F H hs
      (FiniteWired.activeOfSite N x.val (hbox x.val x.property))
      (FiniteWired.activeOfSite N y.val (hbox y.val y.property))

/-- Actual copied reachability agrees with induced raw reachability. -/
theorem reaches_iff_raw_induced (N : ℕ) (F : Finset (Site 2))
    (hbox : ∀ x ∈ F, FiniteWired.inBox N x) (H : Finset (FiniteWired.Edge N))
    (hs : (WiredTrees.graph N).supported (activeLift N (F : Set (Site 2))) H)
    (x y : (F : Set (Site 2))) :
    (WiredTrees.graph N).reaches H (rawVertexLift N F hbox x).val
        (rawVertexLift N F hbox y).val ↔
      ((rawGraph H).induce (F : Set (Site 2))).Reachable x y :=
  (reaches_induced_iff F H hs (rawVertexLift N F hbox x) (rawVertexLift N F hbox y)).trans
    (SimpleGraph.Iso.reachable_iff (φ := insideGraphIso N F hbox H hs))

/-- Deleting a copy deletes exactly its same original coordinate. -/
theorem image_erase_copy {N : ℕ} (H : Finset (FiniteWired.Edge N))
    (e : FiniteWired.Edge N) :
    (H.erase e).image originalCopyEdge = (H.image originalCopyEdge).erase (originalCopyEdge e) :=
  Finset.image_erase (originalCopyEdge_injective N) H e

/-- Raw adjacency after deletion retains exactly the other original coordinates. -/
theorem raw_adjacency_erase_iff {N : ℕ} (H : Finset (FiniteWired.Edge N))
    (e : FiniteWired.Edge N) (x y : Site 2) :
    (rawGraph (H.erase e)).Adj x y ↔
      (rawGraph H).Adj x y ∧ s(x, y) ≠ (originalCopyEdge e).val := by
  constructor
  · rintro ⟨hxy, hpres⟩
    have hm := of_decide_eq_true hpres
    rw [image_erase_copy, Finset.mem_erase] at hm
    refine ⟨⟨hxy, decide_eq_true hm.2⟩, ?_⟩
    intro heq
    exact hm.1 (Subtype.ext heq)
  · rintro ⟨⟨hxy, hpres⟩, hne⟩
    refine ⟨hxy, ?_⟩
    apply decide_eq_true
    rw [image_erase_copy, Finset.mem_erase]
    refine ⟨?_, of_decide_eq_true hpres⟩
    intro h
    exact hne (congrArg Subtype.val h)

/-- Inducing on F and deleting the same raw edge preserves every erased copied path. -/
theorem induced_erase_le_delete {N : ℕ} (F : Finset (Site 2))
    (H : Finset (FiniteWired.Edge N)) (e : FiniteWired.Edge N)
    (u v : (F : Set (Site 2))) (he : (originalCopyEdge e).val = s(u.val, v.val)) :
    ((rawGraph (H.erase e)).induce (F : Set (Site 2))) ≤
      ((rawGraph H).induce (F : Set (Site 2))).deleteEdges {s(u, v)} := by
  intro x y hxy
  have h := (raw_adjacency_erase_iff H e x.val y.val).mp hxy
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨h.1, ?_⟩
  intro hdel
  have hp : s(x.val, y.val) = s(u.val, v.val) :=
    congrArg (Sym2.map (fun z : (F : Set (Site 2)) => z.val))
      (Set.mem_singleton_iff.mp hdel)
  exact h.2 (hp.trans he.symm)


/-- The copied inside-tree clause and the same raw-coordinate inside-tree clause agree.
The raw support condition retains both original endpoints and excludes every exit copy. -/
theorem copied_tree_iff_raw_tree (N : ℕ) (F : Finset (Site 2))
    (hbox : ∀ x ∈ F, FiniteWired.inBox N x) (H : Finset (FiniteWired.Edge N)) :
    (WiredTrees.graph N).is_tree (activeLift N (F : Set (Site 2))) H ↔
      (((toGraph (fun f : LatticeEdge => decide (f ∈ H.image originalCopyEdge))).induce
        (F : Set (Site 2))).IsTree) ∧
      (∀ f ∈ H.image originalCopyEdge, ∃ u ∈ F, ∃ v ∈ F, f.val = s(u, v)) := by
  constructor
  · intro ht
    have hs := ht.2.1
    refine ⟨?_, (supported_iff_raw_endpoints N F hbox H).mp hs⟩
    have hconn : (((WiredTrees.graph N).toSimple H).induce
        (activeLift N (F : Set (Site 2)))).Connected := by
      obtain ⟨v, hv⟩ := ht.1
      letI : Nonempty (activeLift N (F : Set (Site 2))) := ⟨⟨v, hv⟩⟩
      apply SimpleGraph.Connected.mk
      intro x y
      exact (reaches_induced_iff F H hs x y).mp
        (ht.2.2.1 x.val x.property y.val y.property)
    have htree : (((WiredTrees.graph N).toSimple H).induce
        (activeLift N (F : Set (Site 2)))).IsTree :=
      ⟨hconn, ((WiredTrees.graph N).toSimple_isAcyclic ht.2.2.2).induce _⟩
    exact (insideGraphIso N F hbox H hs).isTree_iff.mpr htree
  · rintro ⟨ht, hraw⟩
    have hs := (supported_iff_raw_endpoints N F hbox H).mpr hraw
    obtain ⟨x⟩ := ht.connected.nonempty
    refine ⟨⟨(rawVertexLift N F hbox x).val, (rawVertexLift N F hbox x).property⟩,
      hs, ?_, ?_⟩
    · rintro v ⟨a, rfl, ha⟩ w ⟨b, rfl, hb⟩
      have h := reaches_iff_raw_induced N F hbox H hs
        ⟨FiniteWired.site a, ha⟩ ⟨FiniteWired.site b, hb⟩
      rw [rawVertexLift_site N F hbox a ha, rawVertexLift_site N F hbox b hb] at h
      exact h.mpr (ht.connected ⟨FiniteWired.site a, ha⟩ ⟨FiniteWired.site b, hb⟩)
    · intro e he hreach
      cases e with
      | inl i =>
        have hsup := hs (.inl i) he
        have ha := (some_mem_activeLift N (F : Set (Site 2)) i.val.1).mp hsup.1
        have hb := (some_mem_activeLift N (F : Set (Site 2)) i.val.2).mp hsup.2
        let u : (F : Set (Site 2)) := ⟨FiniteWired.site i.val.1, ha⟩
        let v : (F : Set (Site 2)) := ⟨FiniteWired.site i.val.2, hb⟩
        have hadj : ((rawGraph H).induce (F : Set (Site 2))).Adj u v :=
          (adjacency_iff_raw F H hs i.val.1 i.val.2).mp
            ⟨.inl i, he, Or.inl ⟨rfl, rfl⟩⟩
        have hbridge := SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp ht.isAcyclic hadj
        have hserase : (WiredTrees.graph N).supported (activeLift N (F : Set (Site 2)))
            (H.erase (.inl i)) := by
          intro f hf
          exact hs f (Finset.mem_erase.mp hf).2
        have h := reaches_iff_raw_induced N F hbox (H.erase (.inl i)) hserase u v
        rw [rawVertexLift_site N F hbox i.val.1 ha,
          rawVertexLift_site N F hbox i.val.2 hb] at h
        have hr := h.mp hreach
        exact (SimpleGraph.isBridge_iff.mp hbridge)
          (hr.mono (induced_erase_le_delete F H (.inl i) u v rfl))
      | inr i =>
        exact sink_not_mem_activeLift N (F : Set (Site 2)) (hs (.inr i) he).2

end
end FiniteAvalanches.Trees.Lattice.CurrentInsideRawTree
