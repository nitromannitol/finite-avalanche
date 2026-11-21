import FiniteAvalanches.Wilson.Lattice.RootSampler
import FiniteAvalanches.Wilson.Lattice.SamplerTermination
import FiniteAvalanches.Wilson.Lattice.RowSamplerBridge
import FiniteAvalanches.Wilson.Lattice.BatchRestart
import FiniteAvalanches.Walk.BarlowMasson.SamplerPath

/-! Elementary facts about finite runs of the lattice Wilson sampler.

A run on a concatenated query list is the run on the first list followed by the run on
the second with the remaining rows. An edge whose endpoints are covered is never added
later. Runs from two states with the same covered set make the same hits and attach the
same branches, so they add the same edges. The first row of the iid rows is independent
of the remaining rows. A chain of distinct adjacent sites is the support of a lattice
path. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory ProbabilityTheory Filter FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

theorem samplerRun_append (st : SamplerState) (L M : List (Site 2)) (ξ : ℕ → WalkDriver) :
    samplerRun st (L ++ M) ξ =
      (samplerRun st L ξ).bind (fun s => samplerRun s M (fun i => ξ (i + L.length))) := by
  induction L generalizing st ξ with
  | nil => simp [samplerRun]
  | cons x xs ih =>
    simp only [List.cons_append, samplerRun, List.length_cons]
    cases samplerStep st x (ξ 0) with
    | none => rfl
    | some mid =>
      simp only [Option.bind_some, ih, Nat.add_assoc]

theorem samplerRun_covered_subset {st out : SamplerState} {L : List (Site 2)}
    {ξ : ℕ → WalkDriver} (h : samplerRun st L ξ = some out) : st.covered ⊆ out.covered := by
  induction L generalizing st ξ with
  | nil =>
    have he : st = out := Option.some.inj h
    subst out
    exact Set.Subset.rfl
  | cons x xs ih =>
    cases hs : samplerStep st x (ξ 0) with
    | none => simp [samplerRun, hs] at h
    | some mid =>
      have ht : samplerRun mid xs (fun i => ξ (i + 1)) = some out := by
        simpa only [samplerRun, hs, Option.bind_some] using h
      exact (SamplerState.covered_subset_of_samplerStep hs).trans (ih ht)

theorem fst_mem_dropLast_of_mem_zip_tail :
    ∀ (l : List (Site 2)) {a b : Site 2}, (a, b) ∈ l.zip l.tail → a ∈ l.dropLast
  | [], _, _, h => by simp at h
  | [_], _, _, h => by simp at h
  | u :: v :: r, a, b, h => by
    rw [List.tail_cons, List.zip_cons_cons, List.mem_cons] at h
    rw [List.dropLast_cons_cons]
    rcases h with h | h
    · rw [(Prod.mk.inj h).1]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (fst_mem_dropLast_of_mem_zip_tail (v :: r) h)

theorem walkErase_nodup' (x : Site 2) (w : WalkDriver) (T : ℕ) : (walkErase x w T).Nodup :=
  FiniteAvalanches.Walk.BarlowMasson.walkErase_nodup x w T

/-- Every retained vertex other than the endpoint was visited before the hit. -/
theorem walkErase_dropLast_visited (x : Site 2) (w : WalkDriver) (T : ℕ) (v : Site 2)
    (hv : v ∈ (walkErase x w T).dropLast) : ∃ n < T, position x w n = v := by
  have happ := walkErase_dropLast_append_endpoint x w T
  have hnd := walkErase_nodup' x w T
  rw [← happ] at hnd
  have hne : v ≠ position x w T := by
    intro he
    subst he
    exact (List.disjoint_of_nodup_append hnd) hv (List.mem_singleton_self _)
  have hmem : v ∈ walkErase x w T := List.mem_of_mem_dropLast hv
  obtain ⟨n, hn, hpos⟩ := BatchRestart.walkErase_mem_visited x w T v hmem
  refine ⟨n, lt_of_le_of_ne hn ?_, hpos⟩
  rintro rfl
  exact hne hpos.symm

/-- A new branch has an uncovered endpoint on each of its edges. -/
theorem branchEdges_not_covered {st : SamplerState} {x : Site 2} {w : WalkDriver} {T : ℕ}
    (hT : hitTime st.covered x w = some T) (e : Sym2 (Site 2))
    (he : e ∈ branchEdges (walkErase x w T)) : ∃ v ∈ e, v ∉ st.covered := by
  simp only [branchEdges, List.mem_toFinset, List.mem_map] at he
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := he
  refine ⟨a, Sym2.mem_mk_left a b, ?_⟩
  obtain ⟨n, hn, rfl⟩ := walkErase_dropLast_visited x w T a
    (fst_mem_dropLast_of_mem_zip_tail _ hab)
  exact ((hitTime_eq_some_iff _ _ _ _).mp hT).2 n hn

theorem samplerStep_edge_of_covered {st out : SamplerState} {x : Site 2} {w : WalkDriver}
    (h : samplerStep st x w = some out) (e : Sym2 (Site 2))
    (he : ∀ v ∈ e, v ∈ st.covered) : e ∈ out.edges ↔ e ∈ st.edges := by
  by_cases hx : x ∈ st.covered
  · simp only [samplerStep, if_pos hx, Option.some.injEq] at h
    subst out
    rfl
  · cases hT : hitTime st.covered x w with
    | none => simp [samplerStep, hx, hT] at h
    | some T =>
      simp only [samplerStep, if_neg hx, hT, Option.some.injEq] at h
      subst out
      simp only [Finset.mem_union, or_iff_left_iff_imp]
      intro hb
      obtain ⟨v, hv, hvc⟩ := branchEdges_not_covered hT e hb
      exact (hvc (he v hv)).elim

/-- An edge with both endpoints covered is never added later. -/
theorem samplerRun_edge_of_covered {st out : SamplerState} {L : List (Site 2)}
    {ξ : ℕ → WalkDriver} (h : samplerRun st L ξ = some out) (e : Sym2 (Site 2))
    (he : ∀ v ∈ e, v ∈ st.covered) : e ∈ out.edges ↔ e ∈ st.edges := by
  induction L generalizing st ξ with
  | nil =>
    have hs : st = out := Option.some.inj h
    subst out
    rfl
  | cons x xs ih =>
    cases hs : samplerStep st x (ξ 0) with
    | none => simp [samplerRun, hs] at h
    | some mid =>
      have ht : samplerRun mid xs (fun i => ξ (i + 1)) = some out := by
        simpa only [samplerRun, hs, Option.bind_some] using h
      rw [ih ht (fun v hv => SamplerState.covered_subset_of_samplerStep hs (he v hv)),
        samplerStep_edge_of_covered hs e he]

theorem covered_appendWalkBranch (st : SamplerState) (x : Site 2) (w : WalkDriver) (T : ℕ)
    (hT : position x w T ∈ st.covered) :
    (appendWalkBranch st x w T).covered = {v | v ∈ (walkErase x w T).dropLast} ∪ st.covered := by
  ext v
  simp only [SamplerState.covered, appendWalkBranch, Set.mem_setOf_eq, Set.mem_union]
  by_cases hv : v ∈ (walkErase x w T).dropLast
  · simp only [hv, if_true, true_or, iff_true]
    exact hT
  · simp only [hv, if_false, false_or]

/-- Two states with the same covered set make the same hits and add the same edges. -/
theorem samplerStep_congr {st st' out : SamplerState} (hc : st.covered = st'.covered)
    {x : Site 2} {w : WalkDriver} (h : samplerStep st x w = some out) :
    ∃ out', samplerStep st' x w = some out' ∧ out'.covered = out.covered ∧
      ∃ N, out.edges = st.edges ∪ N ∧ out'.edges = st'.edges ∪ N := by
  by_cases hx : x ∈ st.covered
  · simp only [samplerStep, if_pos hx, Option.some.injEq] at h
    subst out
    refine ⟨st', by rw [samplerStep, if_pos (hc ▸ hx)], hc.symm, ∅, by simp, by simp⟩
  · cases hT : hitTime st.covered x w with
    | none => simp [samplerStep, hx, hT] at h
    | some T =>
      have hT' : hitTime st'.covered x w = some T := hc ▸ hT
      have hpos : ∀ s : SamplerState, hitTime s.covered x w = some T →
          position x w T ∈ s.covered := fun s hs => ((hitTime_eq_some_iff _ _ _ _).mp hs).1
      rw [samplerStep_eq_appendWalkBranch st x w T hx hT, Option.some.injEq] at h
      subst out
      refine ⟨appendWalkBranch st' x w T,
        samplerStep_eq_appendWalkBranch st' x w T (hc ▸ hx) hT', ?_,
        branchEdges (walkErase x w T), rfl, rfl⟩
      rw [covered_appendWalkBranch st x w T (hpos st hT),
        covered_appendWalkBranch st' x w T (hpos st' hT'), hc]

/-- Runs from two states with the same covered set add the same edges. -/
theorem samplerRun_congr {st st' out : SamplerState} (hc : st.covered = st'.covered)
    {L : List (Site 2)} {ξ : ℕ → WalkDriver} (h : samplerRun st L ξ = some out) :
    ∃ out', samplerRun st' L ξ = some out' ∧ out'.covered = out.covered ∧
      ∃ N, out.edges = st.edges ∪ N ∧ out'.edges = st'.edges ∪ N := by
  induction L generalizing st st' ξ with
  | nil =>
    have hs : st = out := Option.some.inj h
    subst out
    exact ⟨st', rfl, hc.symm, ∅, by simp, by simp⟩
  | cons x xs ih =>
    cases hs : samplerStep st x (ξ 0) with
    | none => simp [samplerRun, hs] at h
    | some mid =>
      have ht : samplerRun mid xs (fun i => ξ (i + 1)) = some out := by
        simpa only [samplerRun, hs, Option.bind_some] using h
      obtain ⟨mid', hs', hmc, N₁, hN₁, hN₁'⟩ := samplerStep_congr hc hs
      obtain ⟨out', ho', hoc, N₂, hN₂, hN₂'⟩ := ih hmc.symm ht
      refine ⟨out', by simpa only [samplerRun, hs', Option.bind_some] using ho', hoc,
        N₁ ∪ N₂, ?_, ?_⟩
      · rw [hN₂, hN₁, Finset.union_assoc]
      · rw [hN₂', hN₁', Finset.union_assoc]

/-- The state whose covered set is `S`, with no edges and no history. -/
def coverState (S : Set (Site 2)) : SamplerState where
  colors v := if v ∈ S then some false else none
  edges := ∅
  history := []

theorem coverState_covered (S : Set (Site 2)) : (coverState S).covered = S := by
  ext v
  by_cases hv : v ∈ S <;> simp [SamplerState.covered, coverState, hv]

/-- Planar recurrence: almost surely every walk visits every site. -/
theorem wilsonRows_ae_hits_all :
    ∀ᵐ ξ ∂wilsonRows, ∀ i (x y : Site 2), ∃ n, position x (ξ i) n = y := by
  have hhit (x y : Site 2) : ∀ᵐ w ∂walkLaw, ∃ n, position x w n = y := by
    have hm : MeasurableSet {w : WalkDriver | ∃ n, position x w n = y} := by
      have he : {w : WalkDriver | ∃ n, position x w n = y} =
          ⋃ n : ℕ, {w | position x w n = y} := by ext w; simp
      rw [he]
      exact MeasurableSet.iUnion fun n =>
        (isClosed_eq (continuous_position x n) continuous_const).measurableSet
    exact (mem_ae_iff_prob_eq_one hm).mpr
      (FiniteAvalanches.ProvedStandards.polya_square_lattice_hits_every_site x y)
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro x
  apply ae_all_iff.mpr
  intro y
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => walkLaw) i).quasiMeasurePreserving.ae
    (hhit x y)

/-- The first row is independent of the remaining rows. -/
theorem wilsonRows_head_tail (A : Set WalkDriver) (C : Set (ℕ → WalkDriver))
    (hA : MeasurableSet A) (hC : MeasurableSet C) :
    wilsonRows ({ξ | ξ 0 ∈ A} ∩ {ξ | (fun i => ξ (i + 1)) ∈ C}) = walkLaw A * wilsonRows C := by
  let tail : (ℕ → WalkDriver) → ℕ → WalkDriver := fun ξ i => ξ (i + 1)
  let m : ℕ → MeasurableSpace (ℕ → WalkDriver) := fun i =>
    (inferInstance : MeasurableSpace WalkDriver).comap (fun ξ => ξ i)
  have hm : ∀ i, m i ≤ (inferInstance : MeasurableSpace (ℕ → WalkDriver)) :=
    fun i => (measurable_pi_apply i).comap_le
  have hi : iIndep m wilsonRows :=
    (iIndepFun_infinitePi (X := fun _ a => a) (P := fun _ : ℕ => walkLaw)
      (fun _ => measurable_id)).iIndep
  have hd : Disjoint ({0} : Set ℕ) {i : ℕ | 1 ≤ i} :=
    Set.disjoint_left.mpr (fun i hi hj => by
      simp only [Set.mem_singleton_iff, Set.mem_setOf_eq] at hi hj; omega)
  have h := indep_iSup_of_disjoint hm hi hd
  have hind : IndepFun (fun ξ : ℕ → WalkDriver => ξ 0) tail wilsonRows := by
    change Indep ((inferInstance : MeasurableSpace WalkDriver).comap (fun ξ => ξ 0))
      ((inferInstance : MeasurableSpace (ℕ → WalkDriver)).comap tail) wilsonRows
    apply indep_of_indep_of_le h
    · exact le_iSup₂_of_le 0 (Set.mem_singleton 0) le_rfl
    · rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
      apply iSup_le
      intro i
      rw [MeasurableSpace.comap_comp]
      exact le_iSup₂_of_le (i + 1) (Nat.le_add_left 1 i) le_rfl
  have ht : Measurable tail := measurable_pi_lambda _ (fun i => measurable_pi_apply (i + 1))
  have hlaw : wilsonRows.map tail = wilsonRows :=
    Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => walkLaw)
      (fun _ _ h => Nat.succ_injective h)
  rw [show {ξ : ℕ → WalkDriver | ξ 0 ∈ A} = (fun ξ => ξ 0) ⁻¹' A from rfl,
    show {ξ : ℕ → WalkDriver | (fun i => ξ (i + 1)) ∈ C} = tail ⁻¹' C from rfl,
    hind.measure_inter_preimage_eq_mul A C hA hC,
    ← Measure.map_apply (measurable_pi_apply 0) hA, ← Measure.map_apply ht hC, hlaw,
    show wilsonRows.map (fun ξ => ξ 0) = walkLaw from Measure.infinitePi_map_eval _ 0]

/-- The lattice walk through a chain of adjacent sites. -/
def chainWalk : (u : Site 2) → (l : List (Site 2)) → List.IsChain (lattice 2).Adj (u :: l) →
    (lattice 2).Walk u ((u :: l).getLast (List.cons_ne_nil u l))
  | _, [], _ => SimpleGraph.Walk.nil
  | _, v :: l, h => SimpleGraph.Walk.cons (List.rel_of_isChain_cons_cons h)
      (chainWalk v l (List.isChain_cons_cons.mp h).2)

theorem chainWalk_support : ∀ (u : Site 2) (l : List (Site 2))
    (h : List.IsChain (lattice 2).Adj (u :: l)), (chainWalk u l h).support = u :: l
  | _, [], _ => rfl
  | u, v :: l, h => by
    rw [chainWalk, SimpleGraph.Walk.support_cons]
    exact congrArg (List.cons u) (chainWalk_support v l _)

/-- A chain of distinct adjacent sites from `o` to `z` is the support of a lattice path. -/
theorem exists_path_of_chain {o z : Site 2} (l : List (Site 2))
    (hc : List.IsChain (lattice 2).Adj (o :: l)) (hnd : (o :: l).Nodup)
    (hl : (o :: l).getLast (List.cons_ne_nil o l) = z) :
    ∃ p : (lattice 2).Walk o z, p.IsPath ∧ p.support = o :: l := by
  refine ⟨(chainWalk o l hc).copy rfl hl, ?_, ?_⟩
  · apply SimpleGraph.Walk.IsPath.mk'
    rw [SimpleGraph.Walk.support_copy, chainWalk_support]
    exact hnd
  · rw [SimpleGraph.Walk.support_copy, chainWalk_support]

end

end FiniteAvalanches.Wilson.Lattice
