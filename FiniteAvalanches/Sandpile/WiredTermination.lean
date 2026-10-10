import FiniteAvalanches.Model.LegalLists
import FiniteAvalanches.Sandpile.Observables
import FiniteAvalanches.Model.FiniteWired

/-! Legal single-site topplings in wired square boxes. -/

namespace FiniteAvalanches.Sandpile

open LatticeProb LatticeProb.Sandpile
open scoped Classical

noncomputable section

/-- The active vertices of the literal wired box, as lattice sites. -/
def boxSites (R : ℕ) : Finset Site2 := Finset.univ.image (@FiniteWired.site R)

theorem mem_box_sites (R : ℕ) (x : Site2) :
    x ∈ boxSites R ↔ FiniteWired.inBox R x := by
  constructor
  · intro hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact fun i => (y i).property
  · intro hx
    exact Finset.mem_image.mpr ⟨FiniteWired.activeOfSite R x hx,
      Finset.mem_univ _, rfl⟩

/-- A quadratic barrier before restriction to the wired box. -/
def quadraticBarrier (R K : ℕ) (x : Site2) : ℤ :=
  K * (((R : ℤ) + 1)^2 - (x 0)^2)

theorem quadratic_barrier_nonneg {R K : ℕ} {x : Site2}
    (hx : -(R : ℤ) - 1 ≤ x 0 ∧ x 0 ≤ (R : ℤ) + 1) :
    0 ≤ quadraticBarrier R K x := by
  have hs : 0 ≤ ((R : ℤ) + 1 - x 0) * ((R : ℤ) + 1 + x 0) :=
    mul_nonneg (by omega) (by omega)
  unfold quadraticBarrier
  exact mul_nonneg (Nat.cast_nonneg K) (by nlinarith only [hs])

theorem lap_quadratic_barrier (R K : ℕ) (x : Site2) :
    lap (quadraticBarrier R K) x = -2 * K := by
  simp [lap, nbrSumZ, Fin.sum_univ_two, quadraticBarrier, unit, Pi.single_apply]
  ring

/-- The barrier vanishes outside the active box, as a natural count field. -/
def boxBarrier (R K : ℕ) : Counts :=
  Finsupp.onFinset (boxSites R)
    (fun x => if x ∈ boxSites R then (quadraticBarrier R K x).toNat else 0)
    (by intro x hx; by_contra hn; simp [hn] at hx)

theorem box_barrier_apply_inside {R K : ℕ} {x : Site2} (hx : x ∈ boxSites R) :
    (boxBarrier R K x : ℤ) = quadraticBarrier R K x := by
  have hb := (mem_box_sites R x).mp hx 0
  simp only [boxBarrier, Finsupp.onFinset_apply, if_pos hx]
  exact Int.toNat_of_nonneg (quadratic_barrier_nonneg (by omega))

theorem box_barrier_apply_outside {R K : ℕ} {x : Site2} (hx : x ∉ boxSites R) :
    boxBarrier R K x = 0 := by simp [boxBarrier, hx]

theorem box_barrier_le_quadratic_barrier {R K : ℕ} {x : Site2}
    (hx : -(R : ℤ) - 1 ≤ x 0 ∧ x 0 ≤ (R : ℤ) + 1) :
    (boxBarrier R K x : ℤ) ≤ quadraticBarrier R K x := by
  by_cases hi : x ∈ boxSites R
  · exact le_of_eq (box_barrier_apply_inside hi)
  · rw [box_barrier_apply_outside hi, Nat.cast_zero]
    exact quadratic_barrier_nonneg hx

theorem lap_box_barrier_le {R K : ℕ} {x : Site2} (hx : x ∈ boxSites R) :
    lap (fun y => (boxBarrier R K y : ℤ)) x ≤ -2 * K := by
  have hb := (mem_box_sites R x).mp hx 0
  have hp (i : Fin 2) :
      (boxBarrier R K (x + unit i) : ℤ) ≤ quadraticBarrier R K (x + unit i) := by
    apply box_barrier_le_quadratic_barrier
    fin_cases i <;> simp [unit] <;> omega
  have hm (i : Fin 2) :
      (boxBarrier R K (x - unit i) : ℤ) ≤ quadraticBarrier R K (x - unit i) := by
    apply box_barrier_le_quadratic_barrier
    fin_cases i <;> simp [unit] <;> omega
  calc
    lap (fun y => (boxBarrier R K y : ℤ)) x ≤ lap (quadraticBarrier R K) x := by
      simp only [lap, nbrSumZ, box_barrier_apply_inside hx]
      exact sub_le_sub_right (Finset.sum_le_sum (fun i _ => add_le_add (hp i) (hm i))) _
    _ = -2 * K := lap_quadratic_barrier R K x

theorem legal_list_counts_le_box_barrier {s : Site2 → ℤ} {w : List Site2}
    (hw : LegalList s w) (R K : ℕ) (hwR : ∀ x ∈ w, x ∈ boxSites R)
    (hs : ∀ x ∈ boxSites R, s x < 4 + 2 * K) :
    ∀ x, listCounts w x ≤ boxBarrier R K x := by
  intro x
  have h := wired_legalList_le hw (boxSites R) hwR (boxBarrier R K)
    (fun y hy => by have hb := lap_box_barrier_le (K := K) hy; linarith [hs y hy])
    w.length x
  rw [prefix_eq_terminal w w.length le_rfl] at h
  change (listCounts w x : ℤ) ≤ (boxBarrier R K x : ℤ) at h
  exact_mod_cast h

theorem list_length_le_box_barrier {s : Site2 → ℤ} {w : List Site2}
    (hw : LegalList s w) (R K : ℕ) (hwR : ∀ x ∈ w, x ∈ boxSites R)
    (hs : ∀ x ∈ boxSites R, s x < 4 + 2 * K) :
    w.length ≤ (boxBarrier R K).sum (fun _ n => n) := by
  rw [← listCounts_total]
  exact Finsupp.sum_le_sum_index (legal_list_counts_le_box_barrier hw R K hwR hs)
    (fun _ _ => monotone_id) (fun _ _ => rfl)

theorem legal_list_append_singleton {s : Site2 → ℤ} {w : List Site2}
    (hw : LegalList s w) (x : Site2)
    (hx : 4 ≤ s x + lap (fun y => (listCounts w y : ℤ)) x) :
    LegalList s (w ++ [x]) := by
  intro k hk
  by_cases hkw : k < w.length
  · have ht : prefixCounts (w ++ [x]) k = prefixCounts w k := by
      funext y
      simp only [prefixCounts, List.take_append_of_le_length (Nat.le_of_lt hkw)]
    simpa only [List.getElem_append_left hkw, ht] using hw k hkw
  · have he : k = w.length := by simp only [List.length_append, List.length_singleton] at hk; omega
    subst k
    have ht : prefixCounts (w ++ [x]) w.length = fun y => (listCounts w y : ℤ) := by
      rw [show prefixCounts (w ++ [x]) w.length = prefixCounts w w.length from by
        funext y; simp [prefixCounts]]
      exact prefix_eq_terminal w w.length le_rfl
    simpa [ht] using hx

/-- Every bounded input admits a finite legal wired stabilization. -/
theorem exists_legal_list_stable_in_box (s : Site2 → ℤ) (R K : ℕ)
    (hs : ∀ x ∈ boxSites R, s x < 4 + 2 * K) :
    ∃ w : List Site2, (∀ x ∈ w, x ∈ boxSites R) ∧ LegalList s w ∧
      ∀ x ∈ boxSites R, s x + lap (fun y => (listCounts w y : ℤ)) x < 4 := by
  let P (n : ℕ) := ∃ w : List Site2, w.length = n ∧
    (∀ x ∈ w, x ∈ boxSites R) ∧ LegalList s w
  let B := (boxBarrier R K).sum (fun _ n => n)
  have h0 : P 0 := ⟨[], rfl, by simp, by intro k hk; simp at hk⟩
  obtain ⟨w, hwlen, hwR, hw⟩ := Nat.findGreatest_spec (P := P) (Nat.zero_le B) h0
  refine ⟨w, hwR, hw, ?_⟩
  intro x hx
  by_contra hn
  have hw' := legal_list_append_singleton hw x (by omega)
  have hwR' : ∀ y ∈ w ++ [x], y ∈ boxSites R := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hwR y hy
    · simpa using (List.mem_singleton.mp hy) ▸ hx
  have hb : (w ++ [x]).length ≤ B := list_length_le_box_barrier hw' R K hwR' hs
  have hp : P (w ++ [x]).length := ⟨w ++ [x], rfl, hwR', hw'⟩
  have hm := Nat.le_findGreatest (P := P) hb hp
  simp only [List.length_append, List.length_singleton] at hm
  omega

theorem exists_wired_stabilizes (η : StableField) (ξ : Counts) (R : ℕ) :
    ∃ w, WiredStabilizes η ξ (boxSites R) w := by
  let K := 4 + ξ.sum (fun _ n => n)
  have hξ (x : Site2) : ξ x ≤ ξ.sum (fun _ n => n) := by
    by_cases hx : x ∈ ξ.support
    · exact Finset.single_le_sum (fun y _ => Nat.zero_le (ξ y)) hx
    · simp [Finsupp.notMem_support_iff.mp hx]
  obtain ⟨w, hwR, hw, ht⟩ := exists_legal_list_stable_in_box (initial η ξ) R K
    (fun x _ => by
      have hη := (η x).isLt
      have hb := hξ x
      dsimp [initial, K]
      omega)
  refine ⟨w, hwR, hw, fun x hx => ⟨?_, ht x hx⟩⟩
  have hn := hw.heights_nonneg (initial_nonneg η ξ) w.length x
  rw [prefix_eq_terminal w w.length le_rfl] at hn
  exact hn

theorem card_box_sites (R : ℕ) : (boxSites R).card = (2 * R + 1)^2 := by
  rw [boxSites, Finset.card_image_of_injective _ (FiniteWired.site_injective R),
    Finset.card_univ]
  simp only [FiniteWired.Active, Fintype.card_fun, Fintype.card_fin, Fintype.card_Icc,
    Int.card_Icc]
  congr 1
  omega

theorem box_barrier_le (R K : ℕ) (x : Site2) : boxBarrier R K x ≤ K * (R + 1)^2 := by
  by_cases hx : x ∈ boxSites R
  · have he := box_barrier_apply_inside (K := K) hx
    have hn : (boxBarrier R K x : ℤ) ≤ (K : ℤ) * ((R : ℤ) + 1)^2 := by
      rw [he]
      unfold quadraticBarrier
      exact mul_le_mul_of_nonneg_left (by nlinarith only [sq_nonneg (x 0)])
        (Nat.cast_nonneg K)
    exact_mod_cast hn
  · rw [box_barrier_apply_outside hx]
    exact Nat.zero_le _

theorem sum_box_barrier_le (R K : ℕ) :
    (boxBarrier R K).sum (fun _ n => n) ≤ K * (R + 1)^2 * (2 * R + 1)^2 := by
  rw [Finsupp.sum_of_support_subset (boxBarrier R K)
    (show (boxBarrier R K).support ⊆ boxSites R from Finsupp.support_onFinset_subset)
    (fun _ n => n) (fun _ _ => rfl)]
  calc
    ∑ x ∈ boxSites R, boxBarrier R K x ≤ ∑ _x ∈ boxSites R, K * (R + 1)^2 :=
      Finset.sum_le_sum (fun x _ => box_barrier_le R K x)
    _ = K * (R + 1)^2 * (2 * R + 1)^2 := by
      simp [card_box_sites, Nat.mul_comm]

theorem initial_one_grain_le_four (η : StableField) (o x : Site2) :
    initial η (FiniteAvalanches.oneGrain o) x ≤ 4 := by
  rw [FiniteAvalanches.initial_oneGrain]
  have hη := (η x).isLt
  simp only [dirac]
  split <;> omega

/-- Every legal list confined to a box has the manuscript's explicit count bound. -/
theorem one_grain_legal_list_box_bound (η : StableField) (o : Site2) (R : ℕ)
    {w : List Site2} (hw : LegalList (initial η (FiniteAvalanches.oneGrain o)) w)
    (hwR : ∀ x ∈ w, x ∈ boxSites R) :
    (∀ x, listCounts w x ≤ 2 * (R + 1)^2) ∧ w.length ≤ 8 * (R + 1)^4 := by
  have hs : ∀ x ∈ boxSites R, initial η (FiniteAvalanches.oneGrain o) x < 4 + 2 * (2 : ℕ) :=
    fun x _ => by have h := initial_one_grain_le_four η o x; norm_num; omega
  have hu := legal_list_counts_le_box_barrier hw R 2 hwR hs
  refine ⟨fun x => (hu x).trans (box_barrier_le R 2 x), ?_⟩
  calc
    w.length ≤ (boxBarrier R 2).sum (fun _ n => n) := list_length_le_box_barrier hw R 2 hwR hs
    _ ≤ 2 * (R + 1)^2 * (2 * R + 1)^2 := sum_box_barrier_le R 2
    _ ≤ 8 * (R + 1)^4 := by
      have h : (2 * R + 1)^2 ≤ (2 * (R + 1))^2 := Nat.pow_le_pow_left (by omega) 2
      calc
        2 * (R + 1)^2 * (2 * R + 1)^2 ≤ 2 * (R + 1)^2 * (2 * (R + 1))^2 :=
          Nat.mul_le_mul_left _ h
        _ = 8 * (R + 1)^4 := by ring


end
end FiniteAvalanches.Sandpile
