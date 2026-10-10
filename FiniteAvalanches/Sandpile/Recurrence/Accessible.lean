import FiniteAvalanches.Sandpile.Waves.FiniteAddition
import Mathlib.GroupTheory.Perm.Finite

/-! The globally accessible class of literal finite legal grain additions. -/
namespace FiniteAvalanches.Sandpile.FiniteWired
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves
open scoped Classical BigOperators
noncomputable section

/-- Extend an arbitrary stable input by zero, solely to run wired legal topplings. -/
def extendHeights (N : ℕ) (η : Heights N) : StableField :=
  fun x => if h : inBox N x then η (activeOfSite N x h) else 0

theorem extend_heights_site (N : ℕ) (η : Heights N) (x : Active N) :
    extendHeights N η (site x) = η x := by
  have h : inBox N (site x) := fun i => (x i).property
  rw [extendHeights, dif_pos h]
  congr 1

/-- A grain is added at an actual active source and legally stabilized in the wired box. -/
def AdditionStep {N : ℕ} (η ζ : Heights N) : Prop :=
  ∃ o : Active N, ∃ w : List Site2,
    WiredStabilizes (extendHeights N η) (oneGrain (site o)) (boxSites N) w ∧
      ∀ x : Active N, heightAfter (initial (extendHeights N η) (oneGrain (site o)))
        w (site x) = ((ζ x).val : ℤ)

/-- A finite sequence of actual single-grain additions, allowing the empty sequence. -/
abbrev AdditionReach {N : ℕ} := Relation.ReflTransGen (@AdditionStep N)

theorem addition_step_update {N : ℕ} (η : Heights N) (o : Active N)
    (h : (η o).val < 3) :
    AdditionStep η (Function.update η o ⟨(η o).val+1, by omega⟩) := by
  refine ⟨o, [], ?_, ?_⟩
  · refine ⟨by simp, ?_, ?_⟩
    · intro k hk; simp at hk
    · intro y hy
      have hlo := initial_nonneg (extendHeights N η) (oneGrain (site o)) y
      refine ⟨by simpa [listCounts, lap, nbrSumZ] using hlo, ?_⟩
      by_cases he : y = site o
      · subst y
        simp only [initial, extend_heights_site, oneGrain, Finsupp.single_eq_same]
        simpa [listCounts, lap, nbrSumZ] using
          (show ((η o).val : ℤ) + 1 < 4 by omega)
      · simp only [initial, oneGrain, Finsupp.single_eq_of_ne he]
        simp [listCounts, lap, nbrSumZ]
  · intro x
    by_cases hx : x = o
    · subst x
      simp [heightAfter, initial, oneGrain, extend_heights_site,
        listCounts, lap, nbrSumZ]
    · have hs : site x ≠ site o := fun he => hx (site_injective N he)
      simp [heightAfter, initial, oneGrain, extend_heights_site,
        listCounts, lap, nbrSumZ, hx, hs]

/-- Every stable input and every active source have an actual legal addition endpoint. -/
theorem exists_addition_endpoint {N : ℕ} (η : Heights N) (o : Active N) :
    ∃ ζ : Heights N, ∃ w : List Site2,
      WiredStabilizes (extendHeights N η) (oneGrain (site o)) (boxSites N) w ∧
        ∀ x : Active N, heightAfter (initial (extendHeights N η) (oneGrain (site o)))
          w (site x) = ((ζ x).val : ℤ) := by
  obtain ⟨w,hw⟩ := exists_wired_stabilizes (extendHeights N η) (oneGrain (site o)) N
  let ζ : Heights N := fun x =>
    ⟨(heightAfter (initial (extendHeights N η) (oneGrain (site o))) w (site x)).toNat, by
      have hs := hw.2.2 (site x) (site_mem_box x)
      change 0 ≤ heightAfter (initial (extendHeights N η) (oneGrain (site o))) w (site x) ∧
        heightAfter (initial (extendHeights N η) (oneGrain (site o))) w (site x) < 4 at hs
      omega⟩
  refine ⟨ζ,w,hw,?_⟩
  intro x
  have hs := (hw.2.2 (site x) (site_mem_box x)).1
  exact (Int.toNat_of_nonneg hs).symm

private def deficit {N : ℕ} (η : Heights N) : ℕ := ∑ x : Active N, (3-(η x).val)

private theorem deficit_update_lt {N : ℕ} (η : Heights N) (o : Active N)
    (h : (η o).val < 3) :
    deficit (Function.update η o ⟨(η o).val+1, by omega⟩) < deficit η := by
  unfold deficit
  apply Finset.sum_lt_sum
  · intro x _
    by_cases hx : x = o
    · subst x; simp; omega
    · simp [hx]
  · refine ⟨o, Finset.mem_univ _, ?_⟩
    simp
    omega

theorem addition_reach_allThree {N : ℕ} (η : Heights N) : AdditionReach η (allThree N) := by
  have H : ∀ n : ℕ, ∀ η : Heights N, deficit η = n → AdditionReach η (allThree N) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro η hn
      by_cases he : η = allThree N
      · subst η; exact Relation.ReflTransGen.refl
      · have hex : ∃ o : Active N, (η o).val < 3 := by
          by_contra hno
          apply he
          funext x
          apply Fin.ext
          have hb := (η x).isLt
          have hn := not_exists.mp hno x
          change (η x).val = 3
          omega
        obtain ⟨o, ho⟩ := hex
        let ζ := Function.update η o ⟨(η o).val+1, by omega⟩
        exact (Relation.ReflTransGen.single (addition_step_update η o ho)).trans
          (ih (deficit ζ) (by rw [← hn]; exact deficit_update_lt η o ho) ζ rfl)
  exact H (deficit η) η rfl

private theorem extend_heights_recurrent {N : ℕ} (η : Recurrent N) :
    extendHeights N η.val = zeroExtend N η := rfl

theorem addition_step_equiv {N : ℕ} (o : Active N) (η : Recurrent N) :
    AdditionStep η.val (Waves.finiteAdditionEquiv o η).val := by
  obtain ⟨w, hw, he⟩ := Waves.exists_finite_addition_stabilization o η
  exact ⟨o, w, hw, he⟩

theorem addition_step_preserves_recurrent {N : ℕ} {η ζ : Heights N}
    (hη : recurrent η) (h : AdditionStep η ζ) : recurrent ζ := by
  obtain ⟨o, w, hw, he⟩ := h
  let ηr : Recurrent N := ⟨η,hη⟩
  have hζ : ζ = (Waves.finiteAdditionEquiv o ηr).val := by
    funext x
    apply Fin.ext
    have h := Waves.finite_addition_endpoint o ηr hw x
    have h' := (he x).symm.trans h
    exact_mod_cast h'
  rw [hζ]
  exact (Waves.finiteAdditionEquiv o ηr).property

theorem addition_reach_preserves_recurrent {N : ℕ} {η ζ : Heights N}
    (hη : recurrent η) (h : AdditionReach η ζ) : recurrent ζ := by
  induction h with
  | refl => exact hη
  | @tail b c hab hbc ih => exact addition_step_preserves_recurrent ih hbc

private theorem reach_equiv_iterate {N : ℕ} (o : Active N) (η : Recurrent N) (n : ℕ) :
    AdditionReach η.val (((Waves.finiteAdditionEquiv o)^[n]) η).val := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih.tail (addition_step_equiv o _)

private theorem reverse_step {N : ℕ} {η ζ : Recurrent N}
    (h : AdditionStep η.val ζ.val) : AdditionReach ζ.val η.val := by
  obtain ⟨o, w, hw, he⟩ := h
  have hz : ζ = Waves.finiteAdditionEquiv o η := by
    apply Subtype.ext
    funext x
    apply Fin.ext
    exact_mod_cast (he x).symm.trans (Waves.finite_addition_endpoint o η hw x)
  let e := Waves.finiteAdditionEquiv o
  have hp : 0 < orderOf e := orderOf_pos e
  have hr := reach_equiv_iterate o ζ (orderOf e-1)
  have heq : ((e^[orderOf e-1]) ζ) = η := by
    rw [hz]
    rw [← Function.iterate_succ_apply]
    rw [show (orderOf e-1).succ = orderOf e by omega]
    rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]
    rfl
  change AdditionReach ζ.val (((e^[orderOf e-1]) ζ).val) at hr
  rw [heq] at hr
  exact hr

theorem addition_reach_symm_of_recurrent {N : ℕ} {η ζ : Heights N}
    (hη : recurrent η) (h : AdditionReach η ζ) : AdditionReach ζ η := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hab hbc ih =>
    have hb := addition_reach_preserves_recurrent hη hab
    have hc := addition_step_preserves_recurrent hb hbc
    exact (reverse_step (η := ⟨b,hb⟩) (ζ := ⟨c,hc⟩) hbc).trans ih

/-- These are exactly the stable fields accessible by finite grain additions from every input. -/
theorem recurrent_iff_globally_accessible {N : ℕ} (η : Heights N) :
    recurrent η ↔ ∀ ζ : Heights N, AdditionReach ζ η := by
  constructor
  · intro hη ζ
    exact (addition_reach_allThree ζ).trans
      (addition_reach_symm_of_recurrent hη (addition_reach_allThree η))
  · intro h
    exact addition_reach_preserves_recurrent (allThree_recurrent N) (h (allThree N))

theorem recurrent_iff_reachable_from_allThree {N : ℕ} (η : Heights N) :
    recurrent η ↔ AdditionReach (allThree N) η :=
  ⟨fun h => (recurrent_iff_globally_accessible η).mp h (allThree N),
    addition_reach_preserves_recurrent (allThree_recurrent N)⟩

end
end FiniteAvalanches.Sandpile.FiniteWired
