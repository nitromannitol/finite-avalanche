import FiniteAvalanches.Wilson.Lattice.ContactRestriction
import FiniteAvalanches.Sandpile.LocalConfinement

/-! Finite nested query batches, their complete stopped prefixes, and actual contact failures. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.ActualQueryPrefixes
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory
open BatchRestart ConditionalIteration7 ActualContactHistory ActualContactRestriction
open scoped Classical
noncomputable section

/-- Every list slot uses the original sampler row at that slot. -/
def queryPrefix (Q : ℕ → List (Site 2)) : ℕ → List (Site 2)
  | 0 => []
  | i + 1 => queryPrefix Q i ++ Q i

/-- All vertices of each complete stopped history, including its terminal hit. -/
def localizedPrefix (R : RootPair) (L : List (Site 2)) (h : ℕ) : Set Rows :=
  {ξ | ∃ out, samplerRun (initialSampler R) L ξ = some out ∧
    ∀ p ∈ out.history, ∀ j : Fin (p.length + 1),
      p.vertex j ∈ (boxSites h : Set (Site 2))}

/-- Previous actual contact failures, each with its own localized prior prefix. -/
def survivingPrefixes (R : RootPair) (Q : ℕ → List (Site 2))
    (F : ℕ → Finset (Site 2)) (h : ℕ → ℕ) (t : ℝ) : ℕ → Set Rows
  | 0 => Set.univ
  | i + 1 => (survivingPrefixes R Q F h t i ∩
      localizedPrefix R (queryPrefix Q i) (h i)) \
    continuationContactEvent (initialSampler R) (queryPrefix Q (i + 1)) (F i) t

theorem queryPrefix_length_mono (Q : ℕ → List (Site 2)) :
    Monotone (fun i => (queryPrefix Q i).length) := by
  apply monotone_nat_of_le_succ
  intro i
  simp only [queryPrefix, List.length_append]
  exact Nat.le_add_right _ _

theorem measurable_localizedPrefix_consumed (R : RootPair) (L : List (Site 2)) (h : ℕ) :
    MeasurableSet[consumedRows L.length] (localizedPrefix R L h) :=
  fullHistory_le_consumed R L _ (measurable_completed_observation R L _)

theorem measurable_survivingPrefixes_consumed (R : RootPair) (Q : ℕ → List (Site 2))
    (F : ℕ → Finset (Site 2)) (h : ℕ → ℕ) (t : ℝ) (i : ℕ) :
    MeasurableSet[consumedRows (queryPrefix Q i).length]
      (survivingPrefixes R Q F h t i) := by
  induction i with
  | zero => exact MeasurableSet.univ
  | succ i ih =>
    have hm := consumedRows_mono (queryPrefix_length_mono Q (Nat.le_succ i))
    exact (hm _ (ih.inter (measurable_localizedPrefix_consumed R _ _))).diff
      (measurable_contact_success_consumed R _ _ _)

theorem mem_survivingPrefixes_iff (R : RootPair) (Q : ℕ → List (Site 2))
    (F : ℕ → Finset (Site 2)) (h : ℕ → ℕ) (t : ℝ) (n : ℕ) (ξ : Rows) :
    ξ ∈ survivingPrefixes R Q F h t n ↔ ∀ i < n,
      ξ ∈ localizedPrefix R (queryPrefix Q i) (h i) ∧
      ξ ∉ continuationContactEvent (initialSampler R) (queryPrefix Q (i + 1)) (F i) t := by
  induction n with
  | zero => simp only [survivingPrefixes, Set.mem_univ, Nat.not_lt_zero, IsEmpty.forall_iff,
      implies_true]
  | succ n ih =>
    change (ξ ∈ survivingPrefixes R Q F h t n ∧
      ξ ∈ localizedPrefix R (queryPrefix Q n) (h n)) ∧ _ ↔ _
    rw [ih]
    constructor
    · rintro ⟨⟨hp, hl⟩, hf⟩ i hi
      by_cases hin : i < n
      · exact hp i hin
      · have he : i = n := by omega
        subst i
        exact ⟨hl, hf⟩
    · intro hp
      exact ⟨⟨fun i hi => hp i (Nat.lt_trans hi (Nat.lt_succ_self n)),
        (hp n (Nat.lt_succ_self n)).1⟩, (hp n (Nat.lt_succ_self n)).2⟩

/-- Every original incidence endpoint in the contact count is queried in the next box. -/
theorem contactSites_filter_subset_box (K : Finset (Site 2)) (r : ℕ) :
    contactSites (K.filter (fun x => (siteRadius 0 x : ℝ) ≤ 3 * (r : ℝ))) ⊆
      boxSites (3 * r + 1) := by
  intro y hy
  obtain ⟨x, hx, hy⟩ := Finset.mem_biUnion.mp hy
  have hr : siteRadius 0 x ≤ 3 * r := by
    exact_mod_cast (Finset.mem_filter.mp hx).2
  have hxbox : x ∈ boxSites (3 * r) := by
    rw [mem_box_sites]
    intro i
    have hi := (siteRadius_le_iff 0 x (3 * r)).mp hr i
    simp only [Pi.zero_apply, sub_zero] at hi
    exact abs_le.mp hi
  simp only [nbrFinset, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton] at hy
  obtain ⟨j, rfl | rfl⟩ := hy
  · exact box_sites_add_unit hxbox j
  · exact box_sites_sub_unit hxbox j

end
end FiniteAvalanches.Wilson.Lattice.ActualQueryPrefixes
