import FiniteAvalanches.Wilson.Lattice.WiredObservationLaw

/-! Pathwise identification of wired observations with the lattice sampler. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Every query in a successful finite row history is covered by the lattice sampler. -/
theorem samplerRun_query_covered (st out : SamplerState) (x : ℕ → Site 2)
    (k : Cursor (Site 2)) (N n : ℕ) (rows : ℕ → WalkDriver)
    (hN : ∀ i < n, (rowBranchHistory latticeDirectionHead x st.covered k N rows (i + 1)).2.1 < N)
    (hs : samplerRun st ((List.range n).map x) rows = some out) :
    ∀ i < n, x i ∈ out.covered := by
  obtain ⟨out', hs', hcov⟩ := samplerRun_covered_eq_rowBranchHistory st x k N n rows hN
  have hout : out' = out := Option.some.inj (hs'.symm.trans hs)
  subst out'
  intro i hi
  rw [hcov]
  exact mem_branchHistoryRoots_of_query latticeDirectionHead x st.covered n _ hi

/-- On a confined successful exploration, the ambient edge indicator of a
compatible wired forest agrees with the sampler at each covered interior edge. -/
theorem samplerRun_edgeField_eq_wiredForest_of_confined (R : RootPair) (B N : ℕ)
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
    (e : LatticeEdge) (hebox : ∀ z ∈ e.val, FiniteWired.inBox B z)
    (hecov : ∀ z ∈ e.val, z ∈ out.covered) :
    finiteEdgeField R B (wiredArrowForest R B a) e = decide (e.val ∈ out.edges) := by
  obtain ⟨i, hi⟩ := exists_interiorEdge_of_inBox B e hebox
  have hp := interiorEdge_endpoint_mem i
  have hleft : FiniteWired.site i.val.1 ∈ out.covered := hecov _ (hi ▸ hp.1)
  have hright : FiniteWired.site i.val.2 ∈ out.covered := hecov _ (hi ▸ hp.2)
  have hedge := samplerRun_edge_mem_iff_wiredForest_of_confined R B N x ka kb rows n out
    hN hbox hs a ha i hleft hright
  rw [← hi, finiteEdgeField_internal_eq]
  exact Bool.decide_congr hedge

/-- A confined lattice sampler run and any compatible wired forest have the
same joint observation on all queried edges and colors. -/
theorem samplerRun_jointEvent_iff_wiredObservation_of_confined (R : RootPair) (B N : ℕ)
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
    (E : Finset LatticeEdge) (D : Finset (Site 2)) (pe : LatticeEdge → Bool) (pc : Site 2 → Bool)
    (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z)
    (hD : ∀ z ∈ D, ∃ i < n, x i = z)
    (hebox : ∀ e ∈ E, ∀ z ∈ e.val, FiniteWired.inBox B z)
    (hdbox : ∀ z ∈ D, FiniteWired.inBox B z) :
    (wiredArrowForest R B a ∈ wiredObservationCylinder R B E D pe pc ↔
      (∀ e ∈ E, decide (e.val ∈ out.edges) = pe e) ∧
        ∀ z ∈ D, out.colors z = some (pc z)) := by
  have hinit : (initialSampler R).covered = R.zero ∪ R.one := by
    ext z
    change (if z ∈ R.zero then some false else if z ∈ R.one then some true else none) ≠ none ↔
      (z ∈ R.zero ∨ z ∈ R.one)
    by_cases hz : z ∈ R.zero <;> by_cases ho : z ∈ R.one <;> simp [hz, ho]
  have hsuccess : ∀ i < n,
      (rowBranchHistory latticeDirectionHead x (initialSampler R).covered ka N rows (i + 1)).2.1 < N := by
    simpa only [hinit] using hN
  have hcovered : ∀ i < n, x i ∈ out.covered :=
    samplerRun_query_covered (initialSampler R) out x ka N n rows hsuccess hs
  have hedge (e : LatticeEdge) (he : e ∈ E) :
      finiteEdgeField R B (wiredArrowForest R B a) e = decide (e.val ∈ out.edges) := by
    apply samplerRun_edgeField_eq_wiredForest_of_confined R B N x ka kb rows n out hN hbox hs a ha
      e (hebox e he)
    intro z hz
    obtain ⟨i, hi, hzi⟩ := hE e he z hz
    exact hzi ▸ hcovered i hi
  have hcolor (z : Site 2) (hz : z ∈ D) :
      out.colors z = some (finiteColors R B (wiredArrowForest R B a) (wiredSite B z)) := by
    apply samplerRun_colors_eq_wiredForest_of_confined R B N x ka kb rows n out hN hbox hs a ha
      z (hdbox z hz)
    obtain ⟨i, hi, hzi⟩ := hD z hz
    exact hzi ▸ hcovered i hi
  change ((∀ e ∈ E, finiteEdgeField R B (wiredArrowForest R B a) e = pe e) ∧
      ∀ z ∈ D, finiteColors R B (wiredArrowForest R B a) (wiredSite B z) = pc z) ↔ _
  constructor
  · rintro ⟨he, hd⟩
    exact ⟨fun e he' => (hedge e he').symm.trans (he e he'),
      fun z hz => (hcolor z hz).trans (congrArg some (hd z hz))⟩
  · rintro ⟨he, hd⟩
    refine ⟨fun e he' => (hedge e he').trans (he e he'), ?_⟩
    intro z hz
    exact Option.some.inj ((hcolor z hz).symm.trans (hd z hz))

end
end FiniteAvalanches.Wilson.Lattice
