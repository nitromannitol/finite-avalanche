module

public import FiniteAvalanches.Sandpile.Burning.TreeHeights

@[expose] public section

/-! Decreasing actual burning times construct simple parent paths. Uniqueness of
canonical tree paths then identifies distances and the outgoing original copy.
This is the global geometry needed for the height inverse. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open FiniteAvalanches.Trees.RootedPaths
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [LinearOrder E]
    (G : Multigraph V E) (s : V)

theorem exists_burning_parent_path (h : SourceHeights G s)
    (hn : noForbidden G (Finset.univ.erase s) h) (v : SourceVertex s) :
    ∃ p : ((copiedTreeGraph G).toSimple (parentEdgeSet G s h hn)).Walk v.val s,
      p.IsPath ∧ p.length = burnTime G s h hn v + 1 ∧
      (∀ w : SourceVertex s, w.val ∈ p.support → burnTime G s h hn w ≤ burnTime G s h hn v) ∧
      ((G.left (globalParentCopy G s h hn v).val = v.val ∧
          G.right (globalParentCopy G s h hn v).val = p.snd) ∨
        (G.right (globalParentCopy G s h hn v).val = v.val ∧
          G.left (globalParentCopy G s h hn v).val = p.snd)) := by
  have go : ∀ n : ℕ, ∀ x : SourceVertex s, burnTime G s h hn x = n →
      ∃ p : ((copiedTreeGraph G).toSimple (parentEdgeSet G s h hn)).Walk x.val s,
        p.IsPath ∧ p.length = burnTime G s h hn x + 1 ∧
        (∀ w : SourceVertex s, w.val ∈ p.support → burnTime G s h hn w ≤ burnTime G s h hn x) ∧
        ((G.left (globalParentCopy G s h hn x).val = x.val ∧
            G.right (globalParentCopy G s h hn x).val = p.snd) ∨
          (G.right (globalParentCopy G s h hn x).val = x.val ∧
            G.left (globalParentCopy G s h hn x).val = p.snd)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      have finish : ∀ y : V,
          ((G.left (globalParentCopy G s h hn x).val = x.val ∧
              G.right (globalParentCopy G s h hn x).val = y) ∨
            (G.right (globalParentCopy G s h hn x).val = x.val ∧
              G.left (globalParentCopy G s h hn x).val = y)) →
          ∃ p : ((copiedTreeGraph G).toSimple (parentEdgeSet G s h hn)).Walk x.val s,
            p.IsPath ∧ p.length = burnTime G s h hn x + 1 ∧
            (∀ w : SourceVertex s, w.val ∈ p.support → burnTime G s h hn w ≤ burnTime G s h hn x) ∧
            ((G.left (globalParentCopy G s h hn x).val = x.val ∧
                G.right (globalParentCopy G s h hn x).val = p.snd) ∨
              (G.right (globalParentCopy G s h hn x).val = x.val ∧
                G.left (globalParentCopy G s h hn x).val = p.snd)) := by
        intro y hxy
        have hadj : ((copiedTreeGraph G).toSimple (parentEdgeSet G s h hn)).Adj x.val y :=
          ⟨_, parent_edge_mem G s h hn x, hxy⟩
        rcases global_parent_previous G s h hn x y hxy with hy | ⟨z, hz, ht⟩
        · subst y
          have hm : s ∈ previousBurnt G s h (burnTime G s h hn x) := by
            rcases global_parent_incident G s h hn x with hi | hi <;>
              rcases hxy with he | he <;> aesop
          have hzero : burnTime G s h hn x = 0 := by
            cases he : burnTime G s h hn x with
            | zero => rfl
            | succ m =>
              rw [he, previousBurnt] at hm
              obtain ⟨w, hw, hs⟩ := Finset.mem_image.mp hm
              exact False.elim (source_vertex_ne_sink s w hs)
          refine ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_, ?_, ?_, ?_⟩
          · rw [SimpleGraph.Walk.cons_isPath_iff]
            exact ⟨SimpleGraph.Walk.IsPath.nil, by simpa using source_vertex_ne_sink s x⟩
          · simp [hzero]
          · intro w hw
            have he : w.val = x.val := by
              simpa [source_vertex_ne_sink s w] using hw
            have hwx : w = x := Subtype.ext he
            subst w
            exact le_rfl
          · simpa only [SimpleGraph.Walk.snd_cons] using hxy
        · have hz' : burnTime G s h hn z < n := by omega
          obtain ⟨q, hq, hl, hb, hp⟩ := ih _ hz' z rfl
          have hadj' : ((copiedTreeGraph G).toSimple (parentEdgeSet G s h hn)).Adj x.val z.val := by
            simpa only [hz] using hadj
          have hnot : x.val ∉ q.support := by
            intro hm
            have hb' := hb x hm
            omega
          refine ⟨SimpleGraph.Walk.cons hadj' q, ?_, ?_, ?_, ?_⟩
          · exact (SimpleGraph.Walk.cons_isPath_iff hadj' q).mpr ⟨hq, hnot⟩
          · simp only [SimpleGraph.Walk.length_cons]
            omega
          · intro w hw
            simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
            rcases hw with he | hw
            · have hwx : w = x := Subtype.ext he
              subst w
              exact le_rfl
            · exact (hb w hw).trans (by omega)
          · simpa only [SimpleGraph.Walk.snd_cons, ← hz] using hxy
      rcases global_parent_incident G s h hn x with hl | hr
      · exact finish _ (Or.inl ⟨hl.1, rfl⟩)
      · exact finish _ (Or.inr ⟨hr.1, rfl⟩)
  exact go _ v rfl

theorem tree_distance_burning_tree (h : SourceHeights G s)
    (hn : noForbidden G (Finset.univ.erase s) h) (v : SourceVertex s) :
    treeDistance G s (burningTree G s h hn) v.val = burnTime G s h hn v + 1 := by
  obtain ⟨p, hp, hl, _⟩ := exists_burning_parent_path G s h hn v
  have he := path_eq ((copiedTreeGraph G).toSimple_isTree
    (burningTree G s h hn).property) p hp
  exact (congrArg SimpleGraph.Walk.length he).trans hl

theorem tree_parent_burning_tree (h : SourceHeights G s)
    (hn : noForbidden G (Finset.univ.erase s) h) (v : SourceVertex s) :
    (treeParent G s (burningTree G s h hn) v).val = (globalParentCopy G s h hn v).val := by
  obtain ⟨p, hp, _, _, he⟩ := exists_burning_parent_path G s h hn v
  have hpath := path_eq ((copiedTreeGraph G).toSimple_isTree
    (burningTree G s h hn).property) p hp
  apply ((copiedTreeGraph G).existsUnique_parent_edge
    (burningTree G s h hn) s v.val (source_vertex_ne_sink s v)).unique
  · exact (copiedTreeGraph G).parentEdge_spec (burningTree G s h hn) s v.val
      (source_vertex_ne_sink s v)
  · refine ⟨parent_edge_mem G s h hn v, ?_⟩
    change ((G.left _ = v.val ∧ G.right _ = _) ∨ (G.right _ = v.val ∧ G.left _ = _))
    rw [hpath]
    exact he

end
end FiniteAvalanches.Sandpile.Burning
