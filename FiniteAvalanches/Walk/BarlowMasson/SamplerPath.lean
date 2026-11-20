import FiniteAvalanches.Walk.BarlowMasson.Reentry
import FiniteAvalanches.Walk.BarlowMasson.BoxLaw
import FiniteAvalanches.Wilson.Lattice.SamplerRootPath
import FiniteAvalanches.Wilson.Lattice.SamplerFirstRootPath
import FiniteAvalanches.Wilson.Lattice.TranslationSampler
import FiniteAvalanches.Trees.Lattice.EuclideanPaths

/-!
# Paths of the box sampler between adjacent sites

Run the lattice Wilson sampler rooted at the exterior of the box of size `N`, first from `x` and
then from a neighbour `y` of `x`. The branch of `x` is the loop erasure `β` of the walk from `x`
stopped when it leaves the box. Write `β = α ++ q` with `α` ending at the first site of `β` at
distance at least `k` from `x`. Unless

* (a) some site of `q` is at distance less than `r` from `x`, or
* (b) the walk from `y` reaches distance `r` from `x` before visiting `β`,

the walk from `y` stops at a site `w` of `α` at distance less than `r` from `x`. The part of `α`
from `x` to `w` and the branch of `y` then join `x` and `y` by recorded edges, inside the closed
Euclidean ball of radius `k` about `x`.

## Main statements

* `JoinedIn`: two sites are joined by open edges inside a set of sites.
* `not_mem_treePathLeavesEuclidean_of_joinedIn`: in a tree, sites joined inside a ball have their
  tree path inside the ball.
* `joinedIn_of_samplerRun`: the deterministic statement above.
-/

set_option autoImplicit false

namespace FiniteAvalanches.Walk.BarlowMasson

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Walk.Beurling
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Trees.Lattice.BarlowMasson
open FiniteAvalanches.Wilson.Lattice
open scoped Classical

noncomputable section

theorem euclideanDistance_eq (x z : Site 2) : euclideanDistance x z = euclidNorm (z - x) := by
  simp only [euclideanDistance, euclidNorm, Pi.sub_apply]

/-- `x` and `y` are joined by open edges of `ω` with all their sites in `S`. -/
def JoinedIn (ω : EdgeField) (S : Set (Site 2)) (x y : Site 2) : Prop :=
  ∃ p : (toGraph ω).Walk x y, ∀ z ∈ p.support, z ∈ S

theorem JoinedIn.symm {ω : EdgeField} {S : Set (Site 2)} {x y : Site 2} (h : JoinedIn ω S x y) :
    JoinedIn ω S y x := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p.reverse, fun z hz => ?_⟩
  rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
  exact hp z hz

theorem JoinedIn.trans {ω : EdgeField} {S : Set (Site 2)} {x y z : Site 2} (h : JoinedIn ω S x y)
    (h' : JoinedIn ω S y z) : JoinedIn ω S x z := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨p', hp'⟩ := h'
  refine ⟨p.append p', fun v hv => ?_⟩
  rcases SimpleGraph.Walk.mem_support_append_iff p p' |>.1 hv with h | h
  · exact hp v h
  · exact hp' v h

theorem joinedIn_of_isChain (ω : EdgeField) (S : Set (Site 2)) :
    ∀ (l : List (Site 2)) (a : Site 2), (a :: l).IsChain (toGraph ω).Adj →
      (∀ z ∈ a :: l, z ∈ S) → JoinedIn ω S a ((a :: l).getLast (List.cons_ne_nil a l))
  | [], a, _, hS => ⟨SimpleGraph.Walk.nil, fun z hz => hS z (by simpa using hz)⟩
  | b :: l, a, hc, hS => by
    obtain ⟨p, hp⟩ := joinedIn_of_isChain ω S l b hc.tail fun z hz => hS z (by simp [hz])
    refine ⟨SimpleGraph.Walk.cons hc.rel p, fun z hz => ?_⟩
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hS z (by simp)
    · exact hp z hz

/-- In a tree, sites joined inside the closed Euclidean ball have their tree path inside it. -/
theorem not_mem_treePathLeavesEuclidean_of_joinedIn {ω : EdgeField} {x y : Site 2} {k : ℝ}
    (h : JoinedIn ω (euclideanBall x k) x y) : ω ∉ treePathLeavesEuclidean x y k := by
  rintro ⟨hω, z, hz, hout⟩
  obtain ⟨p, hp⟩ := h
  have hq : treePath ω hω x y = p.bypass :=
    (treePath_full_characterization ω hω x y p.bypass).2 p.bypass_isPath
  rw [hq] at hz
  exact hout (hp z (SimpleGraph.Walk.support_bypass_subset_support p hz))

theorem walkErase_isChain_adj (x : Site 2) (w : ℕ → Dir 2) (T : ℕ) :
    (walkErase x w T).IsChain (lattice 2).Adj := by
  induction T with
  | zero => rw [walkErase_zero']; exact List.isChain_singleton _
  | succ T ih =>
    rw [walkErase_succ', eraseStep_eq]
    by_cases hv : walkPos x w (T + 1) ∈ walkErase x w T
    · exact ih.infix (takeWhile_ne_append_isPrefix hv).isInfix
    · rw [takeWhile_ne_eq_self hv]
      refine ih.append (List.isChain_singleton _) fun a ha b hb => ?_
      rw [List.head?_cons, Option.mem_some_iff] at hb
      subst hb
      rw [List.getLast?_eq_some_getLast (walkErase_ne_nil x w T), Option.mem_some_iff] at ha
      rw [← ha, walkErase_getLast, ← position_eq, ← position_eq]
      exact position_adjacent x w T

/-- A lattice chain whose consecutive pairs are recorded edges is a chain of open edges. -/
theorem isChain_toGraph_of_branchEdges (E : Finset (Sym2 (Site 2))) :
    ∀ l : List (Site 2), l.IsChain (lattice 2).Adj → branchEdges l ⊆ E →
      l.IsChain (toGraph (fun e : LatticeEdge => decide (e.val ∈ E))).Adj
  | [], _, _ => List.IsChain.nil
  | [_], _, _ => List.isChain_singleton _
  | a :: b :: l, hc, hE => by
    have hab : s(a, b) ∈ E := hE (by simp [branchEdges])
    have hrest : branchEdges (b :: l) ⊆ E := by
      intro e he
      apply hE
      simp only [branchEdges, List.mem_toFinset, List.mem_map] at he ⊢
      obtain ⟨p, hp, rfl⟩ := he
      refine ⟨p, ?_, rfl⟩
      simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
      exact Or.inr (by simpa using hp)
    refine List.IsChain.cons_cons ⟨hc.rel, ?_⟩ (isChain_toGraph_of_branchEdges E (b :: l) hc.tail hrest)
    simpa using hab

/-- One successful exploration step from an uncovered site: its stopping time, its edges and
its covered sites. -/
theorem samplerStep_eq_some {st st' : SamplerState} {x : Site 2} {w : WalkDriver}
    (hx : x ∉ st.covered) (h : samplerStep st x w = some st') :
    ∃ T, hitTime st.covered x w = some T ∧
      st'.edges = st.edges ∪ branchEdges (walkErase x w T) ∧
      ∀ v, v ∈ st'.covered ↔ v ∈ st.covered ∨ v ∈ (walkErase x w T).dropLast := by
  cases hT : hitTime st.covered x w with
  | none => simp [samplerStep, hx, hT] at h
  | some T =>
    simp only [samplerStep, if_neg hx, hT, Option.some.injEq] at h
    subst h
    refine ⟨T, rfl, rfl, fun v => ?_⟩
    have hTc := ((hitTime_eq_some_iff _ x w T).1 hT).1
    simp only [SamplerState.covered, Set.mem_setOf_eq] at hTc ⊢
    by_cases hv : v ∈ (walkErase x w T).dropLast
    · simp only [hv, if_true, or_true, iff_true]
      exact hTc
    · simp only [hv, if_false, or_false]

theorem euclidNorm_sub_of_adj {x y : Site 2} (h : (lattice 2).Adj x y) :
    euclidNorm (y - x) = 1 := by
  have hu : ∀ i : Fin 2, euclidNorm (unit i) = 1 := fun i => by
    rw [← dirVec_eq_unit]
    exact euclidNorm_dirVec _
  obtain ⟨i, h | h⟩ := h
  · rw [h, add_sub_cancel_left, hu]
  · rw [h, sub_add_cancel_left, euclidNorm_neg, hu]

theorem joinedIn_take (ω : EdgeField) (S : Set (Site 2)) (a : Site 2) (l : List (Site 2))
    (hc : (a :: l).IsChain (toGraph ω).Adj) (j : ℕ) (hj : j < (a :: l).length)
    (hS : ∀ (m : ℕ) (hm : m ≤ j), (a :: l)[m]'(by omega) ∈ S) :
    JoinedIn ω S a ((a :: l)[j]) := by
  have hpre : a :: l.take j <+: a :: l := by
    rw [← List.take_succ_cons]
    exact List.take_prefix _ _
  have h := joinedIn_of_isChain ω S (l.take j) a (hc.infix hpre.isInfix) (by
    intro z hz
    rw [← List.take_succ_cons] at hz
    obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 hz
    rw [List.getElem_take]
    exact hS m (by simp at hm; omega))
  have hlast : (a :: l.take j).getLast (List.cons_ne_nil a _) = (a :: l)[j] := by
    rw [List.getLast_eq_getElem]
    simp only [← List.take_succ_cons, List.getElem_take]
    congr 1
    simp only [List.length_take, List.length_cons]
    simp at hj
    omega
  rwa [hlast] at h

/-- The exterior of the box of size `N`, seen from `x`. -/
def boxExterior (N : ℕ) (x : Site 2) : Set (Site 2) := {w | ¬FiniteWired.inBox N (w + x)}

/-- The walk from the origin first visits `K` at time `T`. -/
def firstHit (K : Set (Site 2)) (T : ℕ) : Set (ℕ → Dir 2) :=
  {ω | walkPos 0 ω T ∈ K ∧ ∀ s < T, walkPos 0 ω s ∉ K}

/-- The walk from `u` reaches distance `r` from the origin before visiting the sites of `β`. -/
def escapesList (u : Site 2) (r : ℕ) (β : List (Site 2)) : Set (ℕ → Dir 2) :=
  {ω | ∃ t, (r : ℝ) ≤ euclidNorm (walkPos u ω t) ∧ ∀ s < t, walkPos u ω s ∉ β}

/-- Event (a): the branch of `x`, seen from `x`, returns to the disk of radius `r` after its
first site at distance `k`. -/
def reentryRows (N : ℕ) (x : Site 2) (k r : ℕ) : Set (ℕ → WalkDriver) :=
  {ξ | ξ 0 ∈ reentry (boxExterior N x) k r}

/-- Event (b): the walk from `y` reaches distance `r` from `x` before visiting the branch of `x`. -/
def escapeRows (N : ℕ) (x y : Site 2) (r : ℕ) : Set (ℕ → WalkDriver) :=
  {ξ | ∃ T, ξ 0 ∈ firstHit (boxExterior N x) T ∧
    ξ 1 ∈ escapesList (y - x) r (walkErase 0 (ξ 0) T)}

theorem isExitPrefix_take {k : ℕ} (L : List (Site 2)) (hL : ∃ l, L = 0 :: l)
    (hchain : L.IsChain (fun a b => euclidNorm (b - a) ≤ 1)) (i : ℕ)
    (hi : i < L.length) (hk : (k : ℝ) ≤ euclidNorm (L[i]))
    (hmin : ∀ (j : ℕ) (hj : j < i), euclidNorm (L[j]'(by omega)) < k) :
    IsExitPrefix k (L.take (i + 1)) := by
  obtain ⟨l, rfl⟩ := hL
  refine ⟨by simp, by simp, hchain.infix (List.take_prefix _ _).isInfix, ?_, ?_⟩
  · intro a ha
    obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 ha
    simp only [List.length_dropLast, List.length_take] at hm
    rw [List.getElem_dropLast, List.getElem_take]
    exact hmin m (by omega)
  · rw [List.getLast_eq_getElem]
    simp only [List.getElem_take, List.length_take]
    convert hk using 3
    omega

theorem position_eq_walkPos_add (x : Site 2) (w : ℕ → Dir 2) (n : ℕ) :
    position x w n = walkPos 0 w n + x := by
  rw [position_eq, walkPos_eq_add, add_comm]

theorem walkErase_eq_map (x : Site 2) (w : ℕ → Dir 2) (T : ℕ) :
    walkErase x w T = (walkErase 0 w T).map (fun v => v + x) := by
  have h := Translation.walkErase_map 0 x w T
  rwa [zero_add] at h

/-- **The pathwise join.** Unless events (a) or (b) occur, the box sampler joins `x` and `y` by
recorded edges inside the closed Euclidean ball of radius `k` about `x`. -/
theorem joinedIn_of_samplerRun (N k r : ℕ) (x y : Site 2) (hxy : (lattice 2).Adj x y)
    (hr : 2 ≤ r) (hrk : r < k)
    (hbox : ∀ w : Site 2, euclidNorm w < k → FiniteWired.inBox N (w + x))
    (rest : List (Site 2)) (ξ : ℕ → WalkDriver) (out : SamplerState)
    (hrun : samplerRun (initialSampler (sinkRoots N)) (x :: y :: rest) ξ = some out)
    (ha : ξ ∉ reentryRows N x k r) (hb : ξ ∉ escapeRows N x y r) :
    JoinedIn (samplerEdgeField out) (euclideanBall x k) x y := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hrk' : (r : ℝ) < k := by exact_mod_cast hrk
  have hcov0 : ∀ z, z ∈ (initialSampler (sinkRoots N)).covered ↔ ¬FiniteWired.inBox N z := by
    intro z
    rw [initialSampler_covered_roots]
    exact ⟨fun h hz => not_mem_sinkRoots N z hz h, fun h => sinkRoots_ext N z h⟩
  have hin : ∀ z : Site 2, euclidNorm (z - x) < k → FiniteWired.inBox N z := by
    intro z hz
    simpa using hbox (z - x) hz
  have hyx : euclidNorm (y - x) = 1 := euclidNorm_sub_of_adj hxy
  -- the two first steps
  obtain ⟨st1, h1, hrun1⟩ : ∃ st1, samplerStep (initialSampler (sinkRoots N)) x (ξ 0) = some st1 ∧
      samplerRun st1 (y :: rest) (fun i => ξ (i + 1)) = some out := by
    cases h : samplerStep (initialSampler (sinkRoots N)) x (ξ 0) with
    | none => simp [samplerRun, h] at hrun
    | some st1 => exact ⟨st1, rfl, by simpa [samplerRun, h] using hrun⟩
  obtain ⟨st2, h2, hrun2⟩ : ∃ st2, samplerStep st1 y (ξ 1) = some st2 ∧
      samplerRun st2 rest (fun i => ξ (i + 1 + 1)) = some out := by
    cases h : samplerStep st1 y (ξ 1) with
    | none => simp [samplerRun, h] at hrun1
    | some st2 => exact ⟨st2, rfl, by simpa [samplerRun, h] using hrun1⟩
  have h12 : st1.edges ⊆ st2.edges := samplerStep_edges_subset h2
  have h2o : st2.edges ⊆ out.edges := samplerRun_edges_subset hrun2
  have hx0 : x ∉ (initialSampler (sinkRoots N)).covered := by
    rw [hcov0, not_not]
    exact hin x (by rw [sub_self, euclidNorm_zero]; exact_mod_cast (by omega : 0 < k))
  obtain ⟨T0, hT0, hedges1, hcov1⟩ := samplerStep_eq_some hx0 h1
  obtain ⟨hT0c, hT0min⟩ := (hitTime_eq_some_iff _ x (ξ 0) T0).1 hT0
  have hfirst : ξ 0 ∈ firstHit (boxExterior N x) T0 := by
    refine ⟨?_, fun s hs => ?_⟩
    · have := (hcov0 _).1 hT0c
      rwa [position_eq_walkPos_add] at this
    · have := hT0min s hs
      rw [hcov0, not_not, position_eq_walkPos_add] at this
      exact fun h => h this
  set β₀ := walkErase 0 (ξ 0) T0 with hβ₀
  have hβ : walkErase x (ξ 0) T0 = β₀.map (fun v => v + x) := walkErase_eq_map x (ξ 0) T0
  obtain ⟨l0, hl0⟩ := walkErase_start 0 (ξ 0) T0
  have hlen : 0 < β₀.length := List.length_pos_of_ne_nil (walkErase_ne_nil 0 (ξ 0) T0)
  -- the last site of the branch is at distance at least `k`
  have hlast : (k : ℝ) ≤ euclidNorm (β₀[β₀.length - 1]) := by
    have h := walkErase_getLast 0 (ξ 0) T0
    rw [List.getLast_eq_getElem] at h
    rw [h]
    by_contra hlt
    exact hfirst.1 (hbox _ (not_le.1 hlt))
  have hex : ∃ i, ∃ hi : i < β₀.length, (k : ℝ) ≤ euclidNorm (β₀[i]) :=
    ⟨_, by omega, hlast⟩
  set i₀ := Nat.find hex with hi₀def
  obtain ⟨hi₀, hki₀⟩ := Nat.find_spec hex
  have hmin : ∀ (j : ℕ) (hj : j < i₀), euclidNorm (β₀[j]'(by omega)) < k := by
    intro j hj
    have := Nat.find_min hex hj
    simp only [not_exists, not_le] at this
    exact this (by omega)
  -- no reentry
  have hq : ∀ (j : ℕ) (hj : j < β₀.length), i₀ < j → (r : ℝ) ≤ euclidNorm (β₀[j]) := by
    intro j hj hij
    by_contra hlt
    apply ha
    refine ⟨T0, hfirst.1, hfirst.2, β₀.take (i₀ + 1), β₀.drop (i₀ + 1),
      (List.take_append_drop _ _).symm, ?_, β₀[j], ?_, not_le.1 hlt⟩
    · exact isExitPrefix_take (k := k) β₀ ⟨l0, hl0⟩ (walkErase_chain 0 (ξ 0) T0) i₀ hi₀ hki₀ hmin
    · rw [List.mem_iff_getElem]
      exact ⟨j - (i₀ + 1), by simp; omega, by rw [List.getElem_drop]; congr 1; omega⟩
  have hidx : ∀ (j : ℕ) (hj : j < β₀.length), euclidNorm (β₀[j]) < r → j < i₀ := by
    intro j hj hjr
    by_contra hge
    rcases lt_or_eq_of_le (not_lt.1 hge) with h | h
    · linarith [hq j hj h]
    · subst h
      linarith
  -- sites of the branch of `x`
  have hmemβ : ∀ v ∈ walkErase x (ξ 0) T0, ∃ (j : ℕ) (hj : j < β₀.length), v = β₀[j] + x := by
    intro v hv
    rw [hβ, List.mem_map] at hv
    obtain ⟨a, ha', rfl⟩ := hv
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ha'
    exact ⟨j, hj, rfl⟩
  have hβcov : ∀ v ∈ walkErase x (ξ 0) T0, v ∈ st1.covered := by
    intro v hv
    rw [hcov1]
    by_cases hd : v ∈ (walkErase x (ξ 0) T0).dropLast
    · exact Or.inr hd
    · left
      have hv' : v = (walkErase x (ξ 0) T0).getLast (walkErase_ne_nil x (ξ 0) T0) := by
        rw [← List.dropLast_append_getLast (walkErase_ne_nil x (ξ 0) T0), List.mem_append,
          List.mem_singleton] at hv
        exact hv.resolve_left hd
      rw [hv', walkErase_getLast, ← position_eq]
      exact hT0c
  -- the join of `x` with the sites of its branch before the exit
  have hjoinx : ∀ (j : ℕ) (hj : j < β₀.length), j < i₀ →
      JoinedIn (samplerEdgeField out) (euclideanBall x k) x (β₀[j] + x) := by
    intro j hj hji
    obtain ⟨lx, hlx⟩ := walkErase_start x (ξ 0) T0
    have hc : (x :: lx).IsChain (toGraph (samplerEdgeField out)).Adj := by
      rw [← hlx]
      apply isChain_toGraph_of_branchEdges out.edges _ (walkErase_isChain_adj x (ξ 0) T0)
      have hb1 : branchEdges (walkErase x (ξ 0) T0) ⊆ st1.edges := by
        rw [hedges1]
        exact Finset.subset_union_right
      exact hb1.trans (h12.trans h2o)
    have hlenx : (x :: lx).length = β₀.length := by rw [← hlx, hβ, List.length_map]
    have hget : ∀ (m : ℕ) (hm : m < (x :: lx).length), (x :: lx)[m] = β₀[m]'(by omega) + x := by
      intro m hm
      simp only [← hlx, hβ, List.getElem_map]
    have h := joinedIn_take _ (euclideanBall x k) x lx hc j (by omega) (by
      intro m hm
      rw [hget m (by omega)]
      show euclideanDistance x _ ≤ k
      rw [euclideanDistance_eq, add_sub_cancel_right]
      exact (hmin m (by omega)).le)
    rwa [hget j (by omega)] at h
  -- the join of `y` with a site of the branch of `x` before its exit
  obtain ⟨j, hj, hji, hjoiny⟩ : ∃ (j : ℕ) (hj : j < β₀.length), j < i₀ ∧
      JoinedIn (samplerEdgeField out) (euclideanBall x k) y (β₀[j] + x) := by
    by_cases hy : y ∈ st1.covered
    · have hy' : y ∈ walkErase x (ξ 0) T0 := by
        rcases (hcov1 y).1 hy with h | h
        · exact absurd (hin y (by rw [hyx]; exact_mod_cast (by omega : 1 < k))) ((hcov0 y).1 h)
        · exact List.dropLast_subset _ h
      obtain ⟨j, hj, hjy⟩ := hmemβ y hy'
      have hjr : euclidNorm (β₀[j]) < r := by
        have : β₀[j] = y - x := by rw [hjy, add_sub_cancel_right]
        rw [this, hyx]
        linarith
      refine ⟨j, hj, hidx j hj hjr, ?_⟩
      rw [← hjy]
      refine ⟨SimpleGraph.Walk.nil, fun z hz => ?_⟩
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      subst hz
      show euclideanDistance x z ≤ k
      rw [euclideanDistance_eq, hyx]
      exact_mod_cast (by omega : 1 ≤ k)
    · obtain ⟨T1, hT1, hedges2, -⟩ := samplerStep_eq_some hy h2
      obtain ⟨hT1c, hT1min⟩ := (hitTime_eq_some_iff _ y (ξ 1) T1).1 hT1
      have hnear : ∀ s ≤ T1, euclidNorm (position y (ξ 1) s - x) < r := by
        intro s hs
        by_contra hfar
        apply hb
        refine ⟨T0, hfirst, ?_⟩
        by_contra hesc
        apply hesc
        refine ⟨s, ?_, fun s' hs' hmem => ?_⟩
        · have : walkPos (y - x) (ξ 1) s = position y (ξ 1) s - x := by
            rw [position_eq, walkPos_eq_add (y - x), walkPos_eq_add y]
            abel
          rw [this]
          exact not_lt.1 hfar
        · have hpos : position y (ξ 1) s' ∈ walkErase x (ξ 0) T0 := by
            rw [hβ, List.mem_map]
            refine ⟨_, hmem, ?_⟩
            rw [position_eq, walkPos_eq_add (y - x), walkPos_eq_add y]
            abel
          exact hT1min s' (by omega) (hβcov _ hpos)
      have hw : position y (ξ 1) T1 ∈ walkErase x (ξ 0) T0 := by
        rcases (hcov1 _).1 hT1c with h | h
        · exact absurd (hin _ ((hnear T1 le_rfl).trans hrk')) ((hcov0 _).1 h)
        · exact List.dropLast_subset _ h
      obtain ⟨j, hj, hjw⟩ := hmemβ _ hw
      have hjr : euclidNorm (β₀[j]) < r := by
        have : β₀[j] = position y (ξ 1) T1 - x := by rw [hjw, add_sub_cancel_right]
        rw [this]
        exact hnear T1 le_rfl
      refine ⟨j, hj, hidx j hj hjr, ?_⟩
      rw [← hjw]
      obtain ⟨ly, hly⟩ := walkErase_start y (ξ 1) T1
      have hc : (y :: ly).IsChain (toGraph (samplerEdgeField out)).Adj := by
        rw [← hly]
        apply isChain_toGraph_of_branchEdges out.edges _ (walkErase_isChain_adj y (ξ 1) T1)
        rw [hedges2] at h2o
        exact Finset.subset_union_right.trans h2o
      have h := joinedIn_of_isChain _ (euclideanBall x k) ly y hc (by
        intro z hz
        rw [← hly] at hz
        obtain ⟨n, hn, rfl⟩ := walkErase_mem_visited' y (ξ 1) T1 hz
        show euclideanDistance x _ ≤ k
        rw [euclideanDistance_eq, ← position_eq]
        exact ((hnear n hn).trans hrk').le)
      have hl : (y :: ly).getLast (List.cons_ne_nil y ly) = position y (ξ 1) T1 := by
        have := walkErase_getLast y (ξ 1) T1
        simp only [hly] at this
        rw [this, position_eq]
      rwa [hl] at h
  exact (hjoinx j hj hji).trans hjoiny.symm

end

end FiniteAvalanches.Walk.BarlowMasson
