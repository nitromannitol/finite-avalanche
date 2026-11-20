/-
Adapted from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability), module
`LatticeProb/Walk/Beurling/GreenPotential.lean` of the development of the Lawler-Limic Beurling estimate
for Lean v4.35 and its Mathlib.
Changes: imports of the Beurling modules renamed to this repository's; namespace
`LatticeProb.Beurling` renamed to `FiniteAvalanches.Walk.Beurling`, with `open LatticeProb` added;
`Set.mem_ofPred_eq` replaced by `Set.mem_setOf_eq` (once); `measurableSet_setOfPred` replaced by
`measurableSet_setOf` (2 times); `Measurable.of_eval` replaced by `measurable_pi_lambda _` (once);
`dite_eq_left` replaced by `dif_pos` (once); `dite_eq_right` replaced by `dif_neg` (once);
`ite_eq_left` replaced by `if_pos` (once).
-/
import FiniteAvalanches.Walk.Beurling.Defs
import LatticeProb.Walk.RecurrenceHitting
import LatticeProb.Walk.Harnack.Basics
import LatticeProb.Walk.Markov

/-!
# The killed Green function of a finite set through the potential kernel

For a finite set `B ⊂ ℤ²` and `w, z ∈ B`, the Green function of the simple random walk killed on
leaving `B` is
`G_B(w, z) = E^w[a(S_{τ_B} - z)] - a(w - z)`,
where `a` is the potential kernel and `τ_B` is the first time the walk is outside `B`; see
G. F. Lawler and V. Limic, *The Beurling estimate for a class of random walks*,
Electron. J. Probab. 9 (2004), equation (7).

The library's killed Green function `Graph.killedGreenReal` is the expected number of visits
divided by the degree `4`, so the identity carries the factor `4`.

## Main statements

* `exitIdx B w ω`: the first time the walk started at `w` with increments `ω` is outside `B`,
  and `0` when there is no such time.
* `killedGreenReal_eq_potentialKernel`: the identity above.

## Proof

Fix `z ∈ B`. The function `w ↦ 4 G_B(w, z)` vanishes off `B` and, on `B`, has Laplacian
`-4 δ_z`. The function `w ↦ E^w[a(S_{τ_B} - z)] - a(w - z)` also vanishes off `B` (the exit
time is `0` there), and on `B` it has the same Laplacian: the expectation is harmonic on `B` by
the Markov property at time `1`, since from a site of `B` the exit time of the shifted path is one
less and the walk leaves `B` almost surely (it hits every site), while `(P - I) a = δ₀`. The
difference is harmonic on the finite set `B` and vanishes off it, so it vanishes by the maximum
principle.
-/

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb

open MeasureTheory

/-- The first time the walk started at `w` with increments `ω` is outside `B`, and `0` when
there is no such time. -/
noncomputable def exitIdx (B : Finset (Site 2)) (w : Site 2) (ω : ℕ → Dir 2) : ℕ := by
    classical exact if h : ∃ t, walkPos w ω t ∉ B then Nat.find h else 0

section Aux

variable (B : Finset (Site 2)) (z : Site 2)

/-- The first time a position path is outside `B`, and `0` when there is no such time. -/
private noncomputable def pathExitIdx (X : ℕ → Site 2) : ℕ := by
  classical exact if h : ∃ t, X t ∉ B then Nat.find h else 0

/-- `B` together with its lattice neighbours. -/
private def nbhd : Finset (Site 2) :=
  B ∪ B.biUnion fun b => Finset.univ.image fun a : Dir 2 => b + dirVec a

/-- The potential kernel centred at `z`, cut off outside `nbhd B`. -/
private noncomputable def cutKernel (y : Site 2) : ℝ :=
  if y ∈ nbhd B then potentialKernel (y - z) else 0

/-- The cut-off potential kernel at the exit position of a position path. -/
private noncomputable def exitVal (X : ℕ → Site 2) : ℝ :=
  cutKernel B z (X (pathExitIdx B X))

/-- The expected potential kernel at the exit position. -/
private noncomputable def exitMean (y : Site 2) : ℝ :=
  ∫ ω, potentialKernel (walkPos y ω (exitIdx B y ω) - z) ∂pathLaw 2

private theorem walkPos_zero' (y : Site 2) (ω : ℕ → Dir 2) : walkPos y ω 0 = y := by
  simp [walkPos]

private theorem walkPos_succ' (y : Site 2) (ω : ℕ → Dir 2) (s : ℕ) :
    walkPos y ω (s + 1) = walkPos y ω s + dirVec (ω s) := by
  simp only [walkPos, Finset.sum_range_succ, add_assoc]

private theorem exitIdx_eq_pathExitIdx (y : Site 2) (ω : ℕ → Dir 2) :
    exitIdx B y ω = pathExitIdx B (walkPos y ω) := rfl

private theorem exitIdx_of_notMem {y : Site 2} (hy : y ∉ B) (ω : ℕ → Dir 2) :
    exitIdx B y ω = 0 := by
  unfold exitIdx
  split_ifs with h
  · exact (Nat.find_eq_zero h).2 (by simpa only [walkPos_zero'] using hy)
  · rfl

private theorem pathExitIdx_of_exists {X : ℕ → Site 2} (h : ∃ t, X t ∉ B) :
    pathExitIdx B X = Nat.find h := by
  unfold pathExitIdx
  exact dif_pos h

private theorem pathExitIdx_of_not_exists {X : ℕ → Site 2} (h : ¬∃ t, X t ∉ B) :
    pathExitIdx B X = 0 := by
  unfold pathExitIdx
  exact dif_neg h

private theorem mem_nbhd_of_mem {y : Site 2} (hy : y ∈ B) : y ∈ nbhd B :=
  Finset.mem_union_left _ hy

private theorem add_dirVec_mem_nbhd {y : Site 2} (hy : y ∈ B) (a : Dir 2) :
    y + dirVec a ∈ nbhd B :=
  Finset.mem_union_right _
    (Finset.mem_biUnion.2 ⟨y, hy, Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩⟩)

/-- From a site of `nbhd B` the exit position lies in `nbhd B`. -/
private theorem walkPos_exitIdx_mem {y : Site 2} (hy : y ∈ nbhd B) (ω : ℕ → Dir 2) :
    walkPos y ω (exitIdx B y ω) ∈ nbhd B := by
  by_cases hyB : y ∈ B
  · unfold exitIdx
    split_ifs with h
    · have h0 : Nat.find h ≠ 0 := fun h0 => by
        have hs := Nat.find_spec h
        rw [h0, walkPos_zero'] at hs
        exact hs hyB
      obtain ⟨s, hs⟩ : ∃ s, Nat.find h = s + 1 := ⟨Nat.find h - 1, by omega⟩
      have hsB : walkPos y ω s ∈ B := not_not.1 (Nat.find_min h (by omega))
      rw [hs, walkPos_succ']
      exact add_dirVec_mem_nbhd B hsB (ω s)
    · rw [walkPos_zero']
      exact hy
  · rw [exitIdx_of_notMem B hyB, walkPos_zero']
    exact hy

/-- From a site of `B` the exit position of a path that leaves `B` is that of the path shifted
by one step. -/
private theorem apply_pathExitIdx_shift {X : ℕ → Site 2} (h0 : X 0 ∈ B) (h : ∃ t, X t ∉ B) :
    X (pathExitIdx B X) = shiftPath 1 X (pathExitIdx B (shiftPath 1 X)) := by
  have hs : ∀ t, shiftPath 1 X t = X (t + 1) := fun t => by rw [shiftPath, add_comm]
  have h' : ∃ t, shiftPath 1 X t ∉ B := by
    obtain ⟨t, ht⟩ := h
    cases t with
    | zero => exact absurd h0 ht
    | succ s => exact ⟨s, by rwa [hs]⟩
  rw [pathExitIdx_of_exists B h, pathExitIdx_of_exists B h', hs]
  congr 1
  rw [Nat.find_eq_iff]
  refine ⟨?_, fun n hn => ?_⟩
  · have := Nat.find_spec h'
    rwa [hs] at this
  · cases n with
    | zero => exact not_not.2 h0
    | succ m =>
      have := Nat.find_min h' (Nat.succ_lt_succ_iff.1 hn)
      rwa [hs] at this

private theorem measurable_pathExitIdx : Measurable (pathExitIdx B) := by
  refine measurable_to_countable' fun n => ?_
  have hc : ∀ (k : ℕ) (p : Site 2 → Prop), Measurable fun X : ℕ → Site 2 => p (X k) :=
    fun k p => (measurable_of_countable p).comp (measurable_pi_apply k)
  have he : pathExitIdx B ⁻¹' {n} =
      {X | (X n ∉ B ∧ ∀ k, k < n → X k ∈ B) ∨ (n = 0 ∧ ∀ t, X t ∈ B)} := by
    ext X
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    by_cases h : ∃ t, X t ∉ B
    · rw [pathExitIdx_of_exists B h, Nat.find_eq_iff]
      constructor
      · rintro ⟨h1, h2⟩
        exact Or.inl ⟨h1, fun k hk => not_not.1 (h2 k hk)⟩
      · rintro (⟨h1, h2⟩ | ⟨-, h3⟩)
        · exact ⟨h1, fun k hk => not_not.2 (h2 k hk)⟩
        · obtain ⟨t, ht⟩ := h
          exact absurd (h3 t) ht
    · rw [pathExitIdx_of_not_exists B h]
      push Not at h
      constructor
      · rintro rfl
        exact Or.inr ⟨rfl, h⟩
      · rintro (⟨h1, -⟩ | ⟨rfl, -⟩)
        · exact absurd (h n) h1
        · rfl
  rw [he]
  exact measurableSet_setOf.2 (((hc n (· ∉ B)).and (Measurable.forall fun k =>
    hc k (fun y => k < n → y ∈ B))).or (measurable_const.and (Measurable.forall fun t =>
      hc t (· ∈ B))))

private theorem measurable_exitVal : Measurable (exitVal B z) := by
  have hpos : Measurable fun X : ℕ → Site 2 => X (pathExitIdx B X) :=
    (measurable_from_prod_countable_left (f := fun p : (ℕ → Site 2) × ℕ => p.1 p.2)
      fun n => measurable_pi_apply n).comp
      (measurable_id.prodMk (measurable_pathExitIdx B))
  exact (measurable_of_countable (cutKernel B z)).comp hpos

private theorem norm_exitVal_le (X : ℕ → Site 2) :
    ‖exitVal B z X‖ ≤ ∑ s ∈ nbhd B, |potentialKernel (s - z)| := by
  rw [exitVal, cutKernel, Real.norm_eq_abs]
  split_ifs with h
  · exact Finset.single_le_sum (f := fun s => |potentialKernel (s - z)|)
      (fun _ _ => abs_nonneg _) h
  · rw [abs_zero]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _

private theorem exitVal_walkPos {y : Site 2} (hy : y ∈ nbhd B) (ω : ℕ → Dir 2) :
    exitVal B z (walkPos y ω) = potentialKernel (walkPos y ω (exitIdx B y ω) - z) := by
  rw [exitVal, ← exitIdx_eq_pathExitIdx, cutKernel, if_pos (walkPos_exitIdx_mem B hy ω)]

/-- The walk on position paths is the image of the path law of the increments. -/
private theorem integral_siteWalkLaw (y : Site 2) {Φ : (ℕ → Site 2) → ℝ} (hΦ : Measurable Φ) :
    ∫ X, Φ X ∂siteWalkLaw 2 y = ∫ ω, Φ (walkPos y ω) ∂pathLaw 2 := by
  have hm : Measurable fun ξ : ℕ → Dir 2 => fun n => y + ∑ j ∈ Finset.range n, dirVec (ξ j) :=
    measurable_pi_lambda _ fun n => measurable_walkPos y n
  rw [← pathLaw_map_sitePath 2 y, integral_map hm.aemeasurable hΦ.aestronglyMeasurable]
  rfl

private theorem pathExpect_exitVal {y : Site 2} (hy : y ∈ nbhd B) :
    pathExpect 2 (exitVal B z) y = exitMean B z y := by
  rw [pathExpect, integral_siteWalkLaw y (measurable_exitVal B z), exitMean]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => exitVal_walkPos B z hy ω)

/-- The walk leaves the finite set `B` almost surely. -/
private theorem ae_exists_walkPos_notMem (w : Site 2) :
    ∀ᵐ ω ∂pathLaw 2, ∃ t, walkPos w ω t ∉ B := by
  obtain ⟨q, hq⟩ := exists_not_mem_finset (by norm_num : 1 ≤ 2) B
  have hm : MeasurableSet
      {ξ : ℕ → Dir 2 | ∃ n : ℕ, w + ∑ j ∈ Finset.range n, dirVec (ξ j) = q} :=
    measurableSet_setOf.2 (Measurable.exists fun n => measurable_walkPos_pred w (· = q) n)
  have h : ∀ᵐ ξ ∂pathLaw 2, ∃ n : ℕ, w + ∑ j ∈ Finset.range n, dirVec (ξ j) = q :=
    (mem_ae_iff_prob_eq_one hm).2 (pathLaw_two_dim_hit_site w q)
  filter_upwards [h] with ξ hξ
  obtain ⟨n, hn⟩ := hξ
  refine ⟨n, ?_⟩
  rw [walkPos, hn]
  exact hq

private theorem nbrSum_eq_four_mul_walkOp (u : Site 2 → ℝ) (x : Site 2) :
    nbrSum u x = 4 * walkOp u x := by
  rw [walkOp]
  push_cast
  ring

/-- The expected potential kernel at the exit position is harmonic on `B`. -/
private theorem walkOp_exitMean {x : Site 2} (hx : x ∈ B) :
    walkOp (exitMean B z) x = exitMean B z x := by
  have hae : ∀ᵐ ω ∂pathLaw 2,
      exitVal B z (walkPos x ω) = exitVal B z (shiftPath 1 (walkPos x ω)) := by
    filter_upwards [ae_exists_walkPos_notMem B x] with ω hω
    exact congrArg (cutKernel B z)
      (apply_pathExitIdx_shift B (by rw [walkPos_zero']; exact hx) hω)
  have hnbr : ∀ i : Fin 2, x + unit i ∈ nbhd B ∧ x - unit i ∈ nbhd B := by
    intro i
    have h1 := add_dirVec_mem_nbhd B hx (i, true)
    have h2 := add_dirVec_mem_nbhd B hx (i, !true)
    rw [dirVec_eq_unit] at h1
    rw [Bool.not_true, dirVec_eq_neg_unit, ← sub_eq_add_neg] at h2
    exact ⟨h1, h2⟩
  symm
  calc exitMean B z x = ∫ ω, exitVal B z (walkPos x ω) ∂pathLaw 2 :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω =>
          (exitVal_walkPos B z (mem_nbhd_of_mem B hx) ω).symm)
    _ = ∫ ω, exitVal B z (shiftPath 1 (walkPos x ω)) ∂pathLaw 2 := integral_congr_ae hae
    _ = ∫ X, exitVal B z (shiftPath 1 X) ∂siteWalkLaw 2 x :=
        (integral_siteWalkLaw x ((measurable_exitVal B z).comp (measurable_shiftPath 1))).symm
    _ = walkOp^[1] (pathExpect 2 (exitVal B z)) x :=
        integral_comp_shiftPath 2 1 x _ (measurable_exitVal B z) (norm_exitVal_le B z)
    _ = walkOp (exitMean B z) x := by
        rw [Function.iterate_one, walkOp, walkOp, nbrSum, nbrSum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [pathExpect_exitVal B z (hnbr i).1, pathExpect_exitVal B z (hnbr i).2]

/-- Off `B` the expected potential kernel at the exit position is the potential kernel. -/
private theorem exitMean_of_notMem {x : Site 2} (hx : x ∉ B) :
    exitMean B z x = potentialKernel (x - z) := by
  simp [exitMean, exitIdx_of_notMem B hx, walkPos_zero']

/-- The potential kernel centred at `z` solves `(P - I) a(· - z) = δ_z`. -/
private theorem walkOp_potentialKernel_sub_center (x : Site 2) :
    walkOp (fun y => potentialKernel (y - z)) x - potentialKernel (x - z)
      = if x = z then 1 else 0 := by
  have e : walkOp (fun y => potentialKernel (y - z)) x = walkOp potentialKernel (x - z) := by
    rw [walkOp, walkOp, nbrSum, nbrSum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_sub_right_comm, sub_right_comm]
  rw [e, walkOp_potentialKernel_sub]
  by_cases hxz : x = z
  · simp [hxz]
  · simp [hxz, sub_eq_zero]

/-- A function harmonic on the finite set `B` and vanishing off `B` vanishes on `B`. -/
private theorem eq_zero_of_nbrSum (u : Site 2 → ℝ) (hharm : ∀ x ∈ B, nbrSum u x = 4 * u x)
    (hout : ∀ x, x ∉ B → u x = 0) : ∀ x ∈ B, u x = 0 := by
  intro x _
  obtain ⟨q, hq⟩ := exists_not_mem_finset (by norm_num : 1 ≤ 2) B
  have hlap : ∀ c : ℝ, ∀ y ∈ B, y ∉ (∅ : Set (Site 2)) →
      Network.netLaplacian (lattice 2) (Network.unitCond (lattice 2)) (fun v => c * u v) y
        = 0 := by
    intro c y hy _
    rw [Network.netLaplacian_smul, Network.netLaplacian_unitCond,
      laplacian_eq_nbrSum_sub (d := 2) (by norm_num), hharm y hy]
    push_cast
    ring
  have h1 := Network.le_of_harmonicOn (Graph.Zd.latticeConnected 2) Network.isCond_unitCond
    B ∅ (fun v => 1 * u v) 0 hq (hlap 1) (fun y hy => by simp [hout y hy])
    (fun y hy => absurd hy (Set.notMem_empty y)) x
  have h2 := Network.le_of_harmonicOn (Graph.Zd.latticeConnected 2) Network.isCond_unitCond
    B ∅ (fun v => -1 * u v) 0 hq (hlap (-1)) (fun y hy => by simp [hout y hy])
    (fun y hy => absurd hy (Set.notMem_empty y)) x
  have h1' : 1 * u x ≤ 0 := h1
  have h2' : -1 * u x ≤ 0 := h2
  linarith

end Aux

/-- **The killed Green function through the potential kernel** (Lawler and Limic (2004),
equation (7)). For a finite `B ⊂ ℤ²` and `w, z ∈ B`,
`4 G_B(w, z) = E^w[a(S_{τ_B} - z)] - a(w - z)`, where `G_B` is `Graph.killedGreenReal`, the
expected number of visits divided by the degree `4`. -/
theorem killedGreenReal_eq_potentialKernel (B : Finset (Site 2)) {w z : Site 2} (hw : w ∈ B)
    (hz : z ∈ B) :
    4 * Graph.killedGreenReal (lattice 2) (B : Set (Site 2)) w z =
      ∫ ω, potentialKernel (walkPos w ω (exitIdx B w ω) - z) ∂pathLaw 2
        - potentialKernel (w - z) := by
  obtain ⟨q, hq⟩ := exists_not_mem_finset (by norm_num : 1 ≤ 2) B
  have hG := Graph.Zd.latticeConnected 2
  have hsym : (fun y => Graph.killedGreenReal (lattice 2) (B : Set (Site 2)) y z)
      = Graph.killedGreenReal (lattice 2) (B : Set (Site 2)) z :=
    funext fun y => Network.killedGreenReal_symm hG B hq y z
  have hK : ∀ x ∈ B, nbrSum (fun y => Graph.killedGreenReal (lattice 2) (B : Set (Site 2)) y z) x
      = 4 * Graph.killedGreenReal (lattice 2) (B : Set (Site 2)) x z
        - if x = z then 1 else 0 := by
    intro x hx
    have hl := Network.laplacian_killedGreenReal hG B hz hq (v := x) (by exact_mod_cast hx)
    rw [laplacian_eq_nbrSum_sub (d := 2) (by norm_num)] at hl
    rw [hsym, Network.killedGreenReal_symm hG B hq x z]
    push_cast at hl
    split_ifs at hl ⊢ <;> linarith
  have hE : ∀ x ∈ B, nbrSum (exitMean B z) x = 4 * exitMean B z x := fun x hx => by
    rw [nbrSum_eq_four_mul_walkOp, walkOp_exitMean B z hx]
  have hA : ∀ x, nbrSum (fun y => potentialKernel (y - z)) x
      = 4 * potentialKernel (x - z) + 4 * if x = z then 1 else 0 := fun x => by
    rw [nbrSum_eq_four_mul_walkOp, ← walkOp_potentialKernel_sub_center z x]
    ring
  have key := eq_zero_of_nbrSum B (fun y => 4 * Graph.killedGreenReal (lattice 2)
      (B : Set (Site 2)) y z - (exitMean B z y - potentialKernel (y - z)))
    (fun x hx => by
      show nbrSum _ x = 4 * (4 * Graph.killedGreenReal (lattice 2) (B : Set (Site 2)) x z
        - (exitMean B z x - potentialKernel (x - z)))
      have hlin : nbrSum (fun y => 4 * Graph.killedGreenReal (lattice 2) (B : Set (Site 2)) y z
          - (exitMean B z y - potentialKernel (y - z))) x
          = 4 * nbrSum (fun y => Graph.killedGreenReal (lattice 2) (B : Set (Site 2)) y z) x
            - (nbrSum (exitMean B z) x - nbrSum (fun y => potentialKernel (y - z)) x) := by
        simp only [nbrSum, Fin.sum_univ_two]
        ring
      rw [hlin, hK x hx, hE x hx, hA x]
      ring)
    (fun x hx => by
      show 4 * Graph.killedGreenReal (lattice 2) (B : Set (Site 2)) x z
        - (exitMean B z x - potentialKernel (x - z)) = 0
      rw [Network.killedGreenReal_symm hG B hq x z,
        Network.killedGreenReal_eq_zero_of_not_mem hG B hq hx z, exitMean_of_notMem B z hx]
      ring) w hw
  have key' : 4 * Graph.killedGreenReal (lattice 2) (B : Set (Site 2)) w z
      - (exitMean B z w - potentialKernel (w - z)) = 0 := key
  have hmean : exitMean B z w
      = ∫ ω, potentialKernel (walkPos w ω (exitIdx B w ω) - z) ∂pathLaw 2 := rfl
  rw [← hmean]
  linarith

end FiniteAvalanches.Walk.Beurling
