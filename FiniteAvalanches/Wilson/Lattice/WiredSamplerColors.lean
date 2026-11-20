import FiniteAvalanches.Wilson.Lattice.HistoryColorRelabel
import FiniteAvalanches.Wilson.Lattice.SamplerColorPropagation
import FiniteAvalanches.Wilson.Lattice.WiredHistoryColors

/-! Comparison of lattice sampler colors with colors in wired forests. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb Quiver FiniteAvalanches.Wilson FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- The endpoint of a stopped confined wired word is the projection of the
lattice endpoint. -/
theorem wired_historyTrace_endpoint_of_confined (B : ℕ) (x : Site 2)
    (w : WalkDriver) (k : Cursor (FiniteWired.Vertex B)) (t : ℕ)
    (hbox : ∀ i ≤ t, FiniteWired.inBox B (position x w i)) :
    (historyTrace (wiredHead B) (wiredSite B x) (stoppedDirectionHistory (fun _ => t) w)).1 =
      wiredSite B (position x w t) := by
  letI : Quiver (FiniteWired.Vertex B) := instructionQuiver (wiredHead B)
  let p := stoppedDirectionHistory (fun _ => t) w
  have hp : ∀ i < t, p.extend i = w i := by
    intro i hi
    simp only [p, stoppedDirectionHistory, DirectionHistory.extend, dif_pos hi]
  have he := wordTrace_eq_of_prefix (wiredHead B) (wiredSite B x) w p.extend t hp
  change (wordTrace (wiredHead B) (wiredSite B x) p.extend t).1 = _
  rw [he, wordTrace_fst_eq_wordState (wiredHead B) (wiredSite B x) k w]
  exact wiredWordState_eq_of_confined B x w k t hbox t le_rfl

/-- A confined lattice history has compatible finite-box and lattice traces. -/
theorem rowBranchHistory_colorCompatible_of_confined (B N : ℕ) (x : ℕ → Site 2)
    (R : Set (Site 2)) (ka : Cursor (Site 2)) (kb : Cursor (FiniteWired.Vertex B))
    (rows : ℕ → WalkDriver) (n : ℕ)
    (hbox : ∀ i < n, ∀ j ≤ (rowBranchHistory latticeDirectionHead x R ka N rows (i + 1)).2.1,
      FiniteWired.inBox B (position (x i) (rows i) j)) :
    BranchHistory.ColorCompatible (wiredHead B) latticeDirectionHead
      (fun i => wiredSite B (x i)) x (wiredVertexSite B) {v | v ≠ none} n
      (rowBranchHistory latticeDirectionHead x R ka N rows n) := by
  letI : Quiver (FiniteWired.Vertex B) := instructionQuiver (wiredHead B)
  letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
  induction n with
  | zero => trivial
  | succ n ih =>
    have hpast : ∀ i < n, ∀ j ≤ (rowBranchHistory latticeDirectionHead x R ka N rows (i + 1)).2.1,
        FiniteWired.inBox B (position (x i) (rows i) j) :=
      fun i hi => hbox i (Nat.lt_succ_of_lt hi)
    let a := rowBranchHistory latticeDirectionHead x R ka N rows n
    let S := branchHistoryRoots latticeDirectionHead x R n a
    let c := branchHistoryCursor latticeDirectionHead x ka n a
    let t := boundedWordHit latticeDirectionHead S (x n) c N (rows n)
    let p := stoppedDirectionHistory (fun _ => t) (rows n)
    have hconf : ∀ j ≤ t, FiniteWired.inBox B (position (x n) (rows n) j) :=
      hbox n (Nat.lt_succ_self n)
    have he := wired_historyTrace_endpoint_of_confined B (x n) (rows n) kb t hconf
    have ha := historyTrace_stopped_lattice_endpoint (x n) (rows n) t
    have hw := wired_historyTrace_loopErase_of_confined B (x n) (rows n) kb t hconf
    have hl := historyTrace_stopped_loopErase_vertices (x n) (rows n) t
    change BranchHistory.ColorCompatible (wiredHead B) latticeDirectionHead
        (fun i => wiredSite B (x i)) x (wiredVertexSite B) {v | v ≠ none} n a ∧
      (historyTrace (wiredHead B) (wiredSite B (x n)) p).1 ≠ none ∧
      wiredVertexSite B (historyTrace (wiredHead B) (wiredSite B (x n)) p).1 =
        (historyTrace latticeDirectionHead (x n) p).1 ∧
      (loopErase (historyTrace (wiredHead B) (wiredSite B (x n)) p).2).vertices.map (wiredVertexSite B) =
        (loopErase (historyTrace latticeDirectionHead (x n) p).2).vertices
    refine ⟨ih hpast, ?_, ?_, hw.trans hl.symm⟩
    · rw [he, wiredSite, dif_pos (hconf t le_rfl)]
      exact Option.some_ne_none _
    · rw [he, ha, wiredVertexSite_wiredSite B _ (hconf t le_rfl)]

/-- Initial wired colors, including the one-colored exterior vertex. -/
def wiredInitialColor (R : RootPair) (B : ℕ) (v : FiniteWired.Vertex B) : Option Bool :=
  if v ∈ wiredZero R B then some false else if v ∈ wiredOne R B then some true else none

/-- On active vertices the wired initial colors are the lattice initial colors. -/
theorem wiredInitialColor_some (R : RootPair) (B : ℕ) (v : FiniteWired.Active B) :
    wiredInitialColor R B (some v) = (initialSampler R).colors (FiniteWired.site v) := rfl

/-- Every prescribed wired root has its prescribed initial color. -/
theorem wiredInitialColor_root (R : RootPair) (B : ℕ) (v : FiniteWired.Vertex B)
    (hv : v ∈ (wiredRoots R B).val) :
    wiredInitialColor R B v = some (decide (v ∈ wiredOne R B)) := by
  rcases hv with hv | hv
  · have hn : v ∉ wiredOne R B := fun ho => Set.disjoint_left.mp (wired_roots_disjoint R B) hv ho
    simp only [wiredInitialColor, if_pos hv, hn, decide_false]
  · have hn : v ∉ wiredZero R B := fun hz => Set.disjoint_left.mp (wired_roots_disjoint R B) hz hv
    simp only [wiredInitialColor, if_neg hn, hv, if_true, decide_true]

/-- On a confined successful exploration, every compatible wired forest has
the same colors as the lattice sampler at the covered sites inside the box. -/
theorem samplerRun_colors_eq_wiredForest_of_confined (R : RootPair) (B N : ℕ)
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
      (rowBranchHistory latticeDirectionHead x (R.zero ∪ R.one) ka N rows n)) :
    ∀ z, FiniteWired.inBox B z → z ∈ out.covered →
      out.colors z = some (finiteColors R B (wiredArrowForest R B a) (wiredSite B z)) := by
  let roots := R.zero ∪ R.one
  let h := rowBranchHistory latticeDirectionHead x roots ka N rows n
  let bx := fun i => wiredSite B (x i)
  have hinit : (initialSampler R).covered = roots := by
    ext z
    change (if z ∈ R.zero then some false else if z ∈ R.one then some true else none) ≠ none ↔
      (z ∈ R.zero ∨ z ∈ R.one)
    by_cases hz : z ∈ R.zero <;> by_cases ho : z ∈ R.one <;> simp [hz, ho]
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
  have hc := rowBranchHistory_colorCompatible_of_confined B N x roots ka kb rows n hbox
  have hseed : ∀ v ∈ ({v : FiniteWired.Vertex B | v ≠ none} : Set (FiniteWired.Vertex B)),
      wiredInitialColor R B v = (initialSampler R).colors (wiredVertexSite B v) := by
    intro v hv
    cases v with
    | none => exact (hv rfl).elim
    | some v => exact wiredInitialColor_some R B v
  have hmap := branchHistoryColor_map_eq (wiredHead B) latticeDirectionHead bx x
    (wiredVertexSite B) (wiredVertexSite_injective B) {v | v ≠ none}
    (wiredInitialColor R B) (initialSampler R).colors hseed n h hc
  have hhit := GoodArrows.reaches_root (wiredRoots R B).val (wiredHead B) a.val a.property
  have hprop := branchHistoryColor_eq_firstRoot (wiredHead B) bx (wiredRoots R B).val
    (wiredInitialColor R B) (fun v => decide (v ∈ wiredOne R B)) n h a.val hhit
    (wiredInitialColor_root R B) hfirst ha
  have hsuccess : ∀ i < n,
      (rowBranchHistory latticeDirectionHead x (initialSampler R).covered ka N rows (i + 1)).2.1 < N := by
    simpa only [hinit] using hN
  have hsam := samplerRun_colors_eq_branchHistoryColor (initialSampler R) x ka N n rows out hsuccess hs
  obtain ⟨out', hs', hcov⟩ := samplerRun_covered_eq_rowBranchHistory (initialSampler R) x ka N n rows hsuccess
  have hout : out' = out := Option.some.inj (hs'.symm.trans hs)
  subst out'
  rw [hinit] at hcov
  intro z hz hzout
  have hzroots : z ∈ branchHistoryRoots latticeDirectionHead x roots n h := hcov ▸ hzout
  have hzWired : wiredSite B z ∈ branchHistoryRoots (wiredHead B) bx (wiredRoots R B).val n h := by
    have hr := he.2 z hz
    rw [he.1] at hr
    exact hr.mpr hzroots
  have hv : wiredSite B z ≠ none := by
    rw [wiredSite, dif_pos hz]
    exact Option.some_ne_none _
  have hrel := hmap (wiredSite B z) hv
  rw [wiredVertexSite_wiredSite B z hz] at hrel
  have hval := hprop (wiredSite B z) hzWired
  have hcolor : decide (firstRoot (wiredRoots R B).val
      (fun v => wiredHead B v (a.val v)) hhit (wiredSite B z) ∈ wiredOne R B) =
      finiteColors R B (wiredArrowForest R B a) (wiredSite B z) := by
    have hh := finiteColors_arrowForest_eq_true_iff R B a (wiredSite B z)
    dsimp only at hh
    cases hd : decide (firstRoot (wiredRoots R B).val
        (fun v => wiredHead B v (a.val v)) hhit (wiredSite B z) ∈ wiredOne R B) <;>
      cases hf : finiteColors R B (wiredArrowForest R B a) (wiredSite B z) <;>
      simp_all
  rw [hsam, hinit]
  change branchHistoryColor latticeDirectionHead x (initialSampler R).colors n h z = _
  rw [← hrel, hval, hcolor]

end
end FiniteAvalanches.Wilson.Lattice
