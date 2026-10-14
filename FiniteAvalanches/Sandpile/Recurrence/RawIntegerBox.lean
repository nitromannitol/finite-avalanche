import FiniteAvalanches.Sandpile.Recurrence.RawIntegerDynamics
import FiniteAvalanches.Sandpile.Recurrence.Accessible

/-! The boxed accessibility criterion is transported to arbitrary integer inputs. -/
namespace FiniteAvalanches.Sandpile.RawInteger
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves
open scoped Classical BigOperators
noncomputable section

def boxVertex (N : ℕ) (x : FiniteWired.Active N) : boxSites N :=
  ⟨FiniteWired.site x, Waves.site_mem_box x⟩

def boxField {N : ℕ} (η : FiniteWired.Heights N) : Field (boxSites N) :=
  fun x => (η (FiniteWired.activeOfSite N x.val ((mem_box_sites N x.val).mp x.property))).val

theorem box_field_site {N : ℕ} (η : FiniteWired.Heights N) (x : FiniteWired.Active N) :
    boxField η (boxVertex N x) = ((η x).val : ℤ) := by
  have he : FiniteWired.activeOfSite N (FiniteWired.site x)
      ((mem_box_sites N _).mp (boxVertex N x).property) = x :=
    FiniteWired.site_injective N rfl
  exact congrArg (fun y => ((η y).val : ℤ)) he

def boxHeights {N : ℕ} (η : StableState (boxSites N)) (hn : ∀ x, 0 ≤ η.val x) :
    FiniteWired.Heights N := fun x => boundedHeights η hn (boxVertex N x)

theorem box_field_heights {N : ℕ} (η : StableState (boxSites N))
    (hn : ∀ x, 0 ≤ η.val x) : boxField (boxHeights η hn) = η.val := by
  funext x
  exact bounded_heights_value η hn x

theorem box_no_fsc_iff {N : ℕ} (η : FiniteWired.Heights N) :
    NoFSC (boxField η) ↔ FiniteWired.recurrent η := by
  rw [no_fsc_iff_allowed]
  exact (Waves.recurrent_iff_allowed η (extend (boxField η)) (fun x =>
    (extend_site _ (boxVertex N x)).trans (box_field_site η x))).symm

theorem addition_step_reach {N : ℕ} {η ζ : FiniteWired.Heights N}
    (h : FiniteWired.AdditionStep η ζ) : Reach (boxField η) (boxField ζ) := by
  obtain ⟨o, w, hw, he⟩ := h
  let s := initial (FiniteWired.extendHeights N η) (oneGrain (FiniteWired.site o))
  have hs : (fun x : boxSites N => s x.val) = addGrain (boxField η) (boxVertex N o) := by
    funext x
    rw [add_grain_value]
    simp only [s, initial, FiniteWired.extendHeights,
      dif_pos ((mem_box_sites N x.val).mp x.property), oneGrain, Finsupp.single_apply, dirac,
      boxField, boxVertex, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, eq_comm]
    rfl
  have ht : (fun x : boxSites N => heightAfter s w x.val) = boxField ζ := by
    funext x
    exact he (FiniteWired.activeOfSite N x.val ((mem_box_sites N x.val).mp x.property))
  have hr := legal_list_reach s w hw.2.1 hw.1
  rw [hs, ht] at hr
  exact (Relation.ReflTransGen.single (Step.grain _ (boxVertex N o))).trans hr

theorem addition_reach_raw {N : ℕ} {η ζ : FiniteWired.Heights N}
    (h : FiniteWired.AdditionReach η ζ) : Reach (boxField η) (boxField ζ) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.trans (addition_step_reach hstep)

/-- Finite grain filling and an actual legal stabilization handle any integer input. -/
theorem exists_stable_nonnegative_reachable {Γ : Finset Site2} (θ : Field Γ) :
    ∃ ζ : StableState Γ, (∀ x, 0 ≤ ζ.val x) ∧ Reach θ ζ.val := by
  let σ : Field Γ := fun x => max (θ x) 0
  have hσ : ∀ x, 0 ≤ σ x := fun x => le_max_right _ _
  let R := Γ.sup (siteRadius 0)
  have hR : Γ ⊆ boxSites R := fun x hx =>
    (site_radius_zero_le_iff x R).mp (Finset.le_sup (f := siteRadius 0) hx)
  let K := (Finset.univ : Finset Γ).sup (fun x => (σ x).toNat)
  have hbound : ∀ x ∈ Γ, extend σ x < 4 + 2 * K := by
    intro x hx
    simp only [extend, dif_pos hx]
    have hb : (σ ⟨x, hx⟩).toNat ≤ K :=
      Finset.le_sup (f := fun x : Γ => (σ x).toNat) (Finset.mem_univ _)
    have hn := hσ ⟨x, hx⟩
    omega
  obtain ⟨w, hwΓ, hw, ht⟩ := Waves.exists_legal_list_stable_in_subset (extend σ) R K Γ hR hbound
  have hnonneg : ∀ x, 0 ≤ extend σ x := by
    intro x
    unfold extend
    split
    · exact hσ _
    · exact le_refl _
  let ζ : StableState Γ := ⟨fun x => heightAfter (extend σ) w x.val,
    fun x => ht x.val x.property⟩
  have hn : ∀ x, 0 ≤ ζ.val x := by
    intro x
    have h := hw.heights_nonneg hnonneg w.length x.val
    rw [prefix_eq_terminal w w.length le_rfl] at h
    exact h
  have hr := legal_list_reach (extend σ) w hw hwΓ
  have he : (fun x : Γ => extend σ x.val) = σ := funext (extend_site σ)
  rw [he] at hr
  exact ⟨ζ, hn, (reach_fill_negative θ).trans hr⟩

/-- The public stable type imposes only the upper stability bound. Accessibility
quantifies over every integer input, including negative and unstable sandpiles. -/
theorem no_fsc_iff_accessible_box {N : ℕ} (η : StableState (boxSites N)) :
    NoFSC η.val ↔ Accessible η.val := by
  constructor
  · intro ha
    have hn := no_fsc_nonnegative ha
    let ηN := boxHeights η hn
    have hrec : FiniteWired.recurrent ηN :=
      (box_no_fsc_iff ηN).mp (by rw [box_field_heights]; exact ha)
    intro θ
    obtain ⟨ζ, hζ, hr⟩ := exists_stable_nonnegative_reachable θ
    have h := addition_reach_raw
      ((FiniteWired.recurrent_iff_globally_accessible ηN).mp hrec (boxHeights ζ hζ))
    change Reach (boxField (boxHeights ζ hζ)) (boxField (boxHeights η hn)) at h
    rw [box_field_heights, box_field_heights] at h
    exact hr.trans h
  · exact accessible_no_fsc

/-- The actual four direction copies, including distinct sink exits, govern each raw toppling. -/
theorem box_topple_four_directions {N : ℕ} (η : Field (boxSites N))
    (o x : FiniteWired.Active N) :
    topple η (boxVertex N o) (boxVertex N x) = η (boxVertex N x) +
      FiniteWired.wiredLap N
        (fun y => ((oneGrain (FiniteWired.site o)) (FiniteWired.site y) : ℤ)) x := by
  rw [FiniteWired.wired_lap_counts (oneGrain (FiniteWired.site o))
    (by
      intro y hy
      have he : y = FiniteWired.site o := by
        by_contra hh
        exact (Finsupp.mem_support_iff.mp hy) (by
          simp only [oneGrain, Finsupp.single_eq_of_ne hh])
      exact he ▸ Waves.site_mem_box o)]
  have he : (fun y => ((oneGrain (FiniteWired.site o)) y : ℤ)) = dirac (FiniteWired.site o) := by
    funext y
    by_cases hy : y = FiniteWired.site o
    · subst y
      simp only [oneGrain, Finsupp.single_eq_same, dirac_self, Nat.cast_one]
    · simp only [oneGrain, Finsupp.single_eq_of_ne hy, dirac, if_neg hy, Nat.cast_zero]
  rw [he]
  rfl

end
end FiniteAvalanches.Sandpile.RawInteger
