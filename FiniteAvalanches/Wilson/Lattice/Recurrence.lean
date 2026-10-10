import FiniteAvalanches.External.PolyaSquareLattice

set_option autoImplicit false
namespace FiniteAvalanches.External
open LatticeProb MeasureTheory Filter FiniteAvalanches.Wilson.Lattice

theorem box_mono' {M N : ℕ} (h : M ≤ N) : box 2 M ⊆ box 2 N :=
  fun _ hx i => (hx i).trans (by exact_mod_cast h)

theorem exists_box_mem (x : Site 2) : ∃ M : ℕ, x ∈ box 2 M := by
  refine ⟨∑ j, (x j).natAbs, fun i => ?_⟩
  rw [Int.abs_eq_natAbs]
  exact_mod_cast Finset.single_le_sum (f := fun j => (x j).natAbs)
    (fun j _ => Nat.zero_le _) (Finset.mem_univ i)

theorem exists_box_mem_range (X : ℕ → Site 2) (t : ℕ) : ∃ M : ℕ, ∀ s ≤ t, X s ∈ box 2 M := by
  induction t with
  | zero =>
    obtain ⟨M, hM⟩ := exists_box_mem (X 0)
    exact ⟨M, fun s hs => by rw [Nat.le_zero.mp hs]; exact hM⟩
  | succ t ih =>
    obtain ⟨M, hM⟩ := ih
    obtain ⟨M', hM'⟩ := exists_box_mem (X (t + 1))
    refine ⟨max M M', fun s hs => ?_⟩
    rcases Nat.le_succ_iff.mp hs with h | h
    · exact box_mono' (le_max_left _ _) (hM s h)
    · rw [h]; exact box_mono' (le_max_right _ _) hM'

/-- A walk from `x` leaves the box `[-N,N]²` before visiting `a` with probability tending to `0`. -/
theorem srw_exit_before_hit_tendsto_zero (x a : Site 2) :
    Filter.Tendsto
      (fun N : ℕ => walkLaw {X | ∃ t : ℕ, position x X t ∉ box 2 N ∧ ∀ s ≤ t, position x X s ≠ a})
      Filter.atTop (nhds 0) := by
  have hm : ∀ (t : ℕ) (S : Set (Site 2)), MeasurableSet {X : WalkDriver | position x X t ∈ S} :=
    fun t S => (measurable_position x t) (Set.to_countable S).measurableSet
  set E : ℕ → Set WalkDriver :=
    fun N => {X | ∃ t : ℕ, position x X t ∉ box 2 N ∧ ∀ s ≤ t, position x X s ≠ a} with hE
  have hmeas : ∀ N, MeasurableSet (E N) := by
    intro N
    have : E N = ⋃ t : ℕ, ({X | position x X t ∈ (box 2 N)ᶜ} ∩
        ⋂ s ∈ Finset.range (t + 1), {X | position x X s ∈ ({a}ᶜ : Set (Site 2))}) := by
      ext X
      simp only [hE, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter,
        Finset.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨t, h1, h2⟩; exact ⟨t, h1, fun s hs => h2 s (by omega)⟩
      · rintro ⟨t, h1, h2⟩; exact ⟨t, h1, fun s hs => h2 s (by omega)⟩
    rw [this]
    exact MeasurableSet.iUnion fun t =>
      (hm t _).inter (Finset.measurableSet_biInter _ fun s _ => hm s _)
  have hanti : Antitone E := by
    intro M N hMN X hX
    obtain ⟨t, h1, h2⟩ := hX
    exact ⟨t, fun h => h1 (box_mono' hMN h), h2⟩
  have hhitm : MeasurableSet {X : WalkDriver | ∃ t : ℕ, position x X t = a} := by
    have : {X : WalkDriver | ∃ t : ℕ, position x X t = a} = ⋃ t : ℕ, {X | position x X t ∈ ({a} : Set (Site 2))} := by
      ext X; simp
    rw [this]
    exact MeasurableSet.iUnion fun t => hm t _
  have hnever : walkLaw {X : WalkDriver | ∀ t : ℕ, position x X t ≠ a} = 0 := by
    have hc : {X : WalkDriver | ∀ t : ℕ, position x X t ≠ a} = {X : WalkDriver | ∃ t : ℕ, position x X t = a}ᶜ := by
      ext X; simp
    rw [hc]
    exact (prob_compl_eq_zero_iff hhitm).mpr (polya_square_lattice_hits_every_site x a)
  have hnull : walkLaw (⋂ N, E N) = 0 := by
    refine measure_mono_null (fun X hX => ?_) hnever
    intro t ht
    simp only [Set.mem_iInter] at hX
    obtain ⟨M, hM⟩ := exists_box_mem_range (position x X) t
    obtain ⟨t', h1, h2⟩ := hX M
    have htt : t ≤ t' := by
      by_contra hlt
      exact h1 (hM t' (by omega))
    exact h2 t htt ht
  have h := tendsto_measure_iInter_atTop (μ := walkLaw)
    (fun N => (hmeas N).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hnull] at h
  exact h

theorem srw_exit_before_hit_finset_tendsto_zero (x : Site 2) (A : Finset (Site 2))
    (hA : A.Nonempty) :
    Tendsto (fun N : ℕ => walkLaw
      {X | ∃ t : ℕ, position x X t ∉ box 2 N ∧ ∀ s ≤ t, position x X s ∉ (A : Set (Site 2))})
      atTop (nhds 0) := by
  obtain ⟨a, ha⟩ := hA
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (srw_exit_before_hit_tendsto_zero x a) (fun _ => bot_le) (fun N => ?_)
  refine measure_mono ?_
  rintro X ⟨t, h1, h2⟩
  exact ⟨t, h1, fun s hs h => h2 s hs (by rw [h]; exact Finset.mem_coe.mpr ha)⟩


end FiniteAvalanches.External
