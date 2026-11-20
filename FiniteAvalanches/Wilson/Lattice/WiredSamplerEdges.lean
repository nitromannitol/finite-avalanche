import FiniteAvalanches.Wilson.Lattice.WiredHistoryInteriorEdges
import FiniteAvalanches.Wilson.Lattice.WiredSamplerColors

/-! Comparison of lattice sampler edges with interior wired forest edges. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- A confined successful lattice exploration and every compatible wired
forest agree on each interior edge whose endpoints have been covered. -/
theorem samplerRun_edge_mem_iff_wiredForest_of_confined (R : RootPair) (B N : ℕ)
    (x : ℕ → Site 2) (ka : Cursor (Site 2)) (kb : Cursor (FiniteWired.Vertex B))
    (rows : ℕ → WalkDriver) (n : ℕ) (out : SamplerState)
    (hN : ∀ i < n,
      (rowBranchHistory latticeDirectionHead x (R.zero ∪ R.one) ka N rows (i + 1)).2.1 < N)
    (hbox : ∀ i < n, ∀ j ≤
      (rowBranchHistory latticeDirectionHead x (R.zero ∪ R.one) ka N rows (i + 1)).2.1,
      FiniteWired.inBox B (position (x i) (rows i) j))
    (hs : samplerRun (initialSampler R) ((List.range n).map x) rows = some out)
    (a : GoodArrows (wiredRoots R B).val (wiredHead B))
    (ha : BranchHistory.Realizes (wiredHead B) (fun i => wiredSite B (x i)) a.val n
      (rowBranchHistory latticeDirectionHead x (R.zero ∪ R.one) ka N rows n))
    (e : FiniteWired.InteriorEdge B)
    (hleft : FiniteWired.site e.val.1 ∈ out.covered)
    (hright : FiniteWired.site e.val.2 ∈ out.covered) :
    Sum.inl e ∈ (wiredArrowForest R B a).val ↔ (interiorEdge e).val ∈ out.edges := by
  let roots := R.zero ∪ R.one
  let h := rowBranchHistory latticeDirectionHead x roots ka N rows n
  let bx := fun i => wiredSite B (x i)
  have hinit : (initialSampler R).covered = roots := by
    ext z
    change (if z ∈ R.zero then some false else if z ∈ R.one then some true else none) ≠ none ↔
      (z ∈ R.zero ∨ z ∈ R.one)
    by_cases hz : z ∈ R.zero <;> by_cases ho : z ∈ R.one <;> simp [hz, ho]
  have hsuccess : ∀ i < n,
      (rowBranchHistory latticeDirectionHead x (initialSampler R).covered ka N rows (i + 1)).2.1 < N := by
    simpa only [hinit] using hN
  have hwire (i : ℕ) (hi : i < n) :
      (rowBranchHistory (wiredHead B) bx (wiredRoots R B).val kb N rows (i + 1)).2.1 < N := by
    have hn' : ∀ j < i + 1,
        (rowBranchHistory latticeDirectionHead x roots ka N rows (j + 1)).2.1 < N :=
      fun j hj => hN j (lt_of_lt_of_le hj (Nat.succ_le_of_lt hi))
    have hb' : ∀ j < i + 1, ∀ q ≤
        (rowBranchHistory latticeDirectionHead x roots ka N rows (j + 1)).2.1,
        FiniteWired.inBox B (position (x j) (rows j) q) :=
      fun j hj => hbox j (lt_of_lt_of_le hj (Nat.succ_le_of_lt hi))
    have he := (rowBranchHistory_wired_eq_of_confined B N x (wiredRoots R B).val roots
      kb ka rows (i + 1) (wiredRoots_wiredSite_iff R B) hn' hb').1
    rw [he]
    exact hN i hi
  have he := rowBranchHistory_wired_eq_of_confined B N x (wiredRoots R B).val roots
    kb ka rows n (wiredRoots_wiredSite_iff R B) hN hbox
  have hfirst := rowBranchHistory_firstHits_of_hits (wiredHead B) bx (wiredRoots R B).val kb N n rows hwire
  rw [he.1] at hfirst
  obtain ⟨out', hs', hcov⟩ := samplerRun_covered_eq_rowBranchHistory (initialSampler R) x ka N n rows hsuccess
  have hout : out' = out := Option.some.inj (hs'.symm.trans hs)
  subst out'
  rw [hinit] at hcov
  have hsiteBox (v : FiniteWired.Active B) : FiniteWired.inBox B (FiniteWired.site v) :=
    fun i => (v i).property
  have hwireRoot (v : FiniteWired.Active B) (hv : FiniteWired.site v ∈ out.covered) :
      some v ∈ branchHistoryRoots (wiredHead B) bx (wiredRoots R B).val n h := by
    have hlat : FiniteWired.site v ∈ branchHistoryRoots latticeDirectionHead x roots n h := hcov ▸ hv
    have hr := he.2 (FiniteWired.site v) (hsiteBox v)
    rw [he.1] at hr
    have hs : wiredSite B (FiniteWired.site v) = some v := by
      simpa only [wiredVertexSite] using wiredSite_wiredVertexSite B (some v)
    rw [hs] at hr
    exact hr.mpr hlat
  have hi := wiredInterior_mem_iff_branchHistoryEdgeSet R B bx n h a e hfirst ha
    (hwireRoot e.val.1 hleft) (hwireRoot e.val.2 hright)
  have hc := rowBranchHistory_colorCompatible_of_confined B N x roots ka kb rows n hbox
  have hmap := branchHistoryEdgeSet_map_eq (wiredHead B) latticeDirectionHead bx x
    (wiredVertexSite B) {v | v ≠ none} n h hc
  have hsam := samplerRun_edges_eq_branchHistoryEdgeSet (initialSampler R) x ka N n rows out hsuccess hs
  rw [hinit] at hsam
  have hsam' : out.edges = branchHistoryEdgeSet latticeDirectionHead x n h := by
    simpa only [initialSampler, Finset.empty_union] using hsam
  have hm : s(some e.val.1, some e.val.2) ∈ branchHistoryEdgeSet (wiredHead B) bx n h ↔
      (interiorEdge e).val ∈ branchHistoryEdgeSet latticeDirectionHead x n h := by
    rw [← hmap, Finset.mem_image]
    constructor
    · intro hv
      exact ⟨s(some e.val.1, some e.val.2), hv, rfl⟩
    · rintro ⟨q, hq, hqeq⟩
      have hq' : q = s(some e.val.1, some e.val.2) :=
        Sym2.map.injective (wiredVertexSite_injective B) hqeq
      exact hq' ▸ hq
  exact hi.trans (hm.trans (by rw [hsam']))

end
end FiniteAvalanches.Wilson.Lattice
