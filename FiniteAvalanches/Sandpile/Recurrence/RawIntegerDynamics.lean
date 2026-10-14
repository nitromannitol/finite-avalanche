import FiniteAvalanches.Sandpile.Recurrence.RawIntegerCarrier
import FiniteAvalanches.Model.WiredLaplacian

/-! Single grains and legal single-site topplings on the whole integer carrier. -/
namespace FiniteAvalanches.Sandpile.RawInteger
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves
open scoped Classical BigOperators
noncomputable section

def addGrain {Γ : Finset Site2} (η : Field Γ) (o : Γ) : Field Γ :=
  Function.update η o (η o + 1)

theorem add_grain_value {Γ : Finset Site2} (η : Field Γ) (o x : Γ) :
    addGrain η o x = η x + dirac o.val x.val := by
  by_cases hx : x = o
  · subst x
    simp only [addGrain, Function.update_self, dirac_self]
  · have hv : x.val ≠ o.val := fun he => hx (Subtype.ext he)
    simp only [addGrain, Function.update_of_ne hx, dirac_of_ne hv, add_zero]

def topple {Γ : Finset Site2} (η : Field Γ) (o : Γ) : Field Γ :=
  fun x => η x + lap (dirac o.val) x.val

inductive Step (Γ : Finset Site2) : Field Γ → Field Γ → Prop
  | grain (η : Field Γ) (o : Γ) : Step Γ η (addGrain η o)
  | fire (η : Field Γ) (o : Γ) (hu : 4 ≤ η o) : Step Γ η (topple η o)

abbrev Reach {Γ : Finset Site2} := Relation.ReflTransGen (Step Γ)
def Accessible {Γ : Finset Site2} (η : Field Γ) : Prop := ∀ θ : Field Γ, Reach θ η

theorem step_preserves_nonnegative {Γ : Finset Site2} {η ζ : Field Γ}
    (hn : ∀ x, 0 ≤ η x) (h : Step Γ η ζ) : ∀ x, 0 ≤ ζ x := by
  cases h with
  | grain o =>
    intro x
    rw [add_grain_value]
    exact add_nonneg (hn x) (dirac_nonneg _ _)
  | fire o hu =>
    intro x
    by_cases hx : x = o
    · subst x
      simp only [topple, lap_dirac_self]
      omega
    · exact add_nonneg (hn x) (lap_dirac_nonneg (fun he => hx (Subtype.ext he)))

theorem reach_preserves_nonnegative {Γ : Finset Site2} {η ζ : Field Γ}
    (hn : ∀ x, 0 ≤ η x) (h : Reach η ζ) : ∀ x, 0 ≤ ζ x := by
  induction h with
  | refl => exact hn
  | tail _ hstep ih => exact step_preserves_nonnegative ih hstep

theorem step_preserves_no_fsc {Γ : Finset Site2} {η ζ : Field Γ}
    (ha : NoFSC η) (h : Step Γ η ζ) : NoFSC ζ := by
  cases h with
  | grain o =>
    intro A hA hf
    apply ha A hA
    refine ⟨hf.1, ?_⟩
    intro x hx
    have ht := hf.2 x hx
    rw [add_grain_value] at ht
    change η ⟨x, hA hx⟩ + dirac o.val x < (Waves.degree A x : ℤ) at ht
    have hd := dirac_nonneg o.val x
    omega
  | fire o hu =>
    have hn := step_preserves_nonnegative (no_fsc_nonnegative ha) (Step.fire η o hu)
    have hb : Waves.allowed Γ (fun x => extend η x + lap (dirac o.val) x) :=
      Waves.allowed_topple ((no_fsc_iff_allowed η).mp ha) (fun x hx => by
        simpa only [extend, dif_pos hx, topple] using hn ⟨x, hx⟩)
    apply (no_fsc_iff_allowed _).mpr
    exact (Waves.allowed_congr (fun x hx => by
      simp only [extend, dif_pos hx, topple])).mp hb

theorem reach_preserves_no_fsc {Γ : Finset Site2} {η ζ : Field Γ}
    (ha : NoFSC η) (h : Reach η ζ) : NoFSC ζ := by
  induction h with
  | refl => exact ha
  | tail _ hstep ih => exact step_preserves_no_fsc ih hstep

theorem accessible_no_fsc {Γ : Finset Site2} {η : Field Γ} (h : Accessible η) : NoFSC η := by
  let a : AllowedState Γ := Classical.choice inferInstance
  exact reach_preserves_no_fsc a.property (h a.val.val)

theorem negative_not_accessible {Γ : Finset Site2} (η : Field Γ) (x : Γ)
    (hx : η x < 0) : ¬Accessible η := by
  intro ha
  have hn := reach_preserves_nonnegative (η := fun _ : Γ => (0 : ℤ))
    (fun _ => le_refl _) (ha (fun _ => 0)) x
  omega

private def grainDeficit {Γ : Finset Site2} (η ζ : Field Γ) : ℕ :=
  ∑ x : Γ, (ζ x - η x).toNat

/-- Every coordinatewise increase is a finite word of actual single-grain additions. -/
theorem reach_of_le {Γ : Finset Site2} (η ζ : Field Γ) (hle : ∀ x, η x ≤ ζ x) :
    Reach η ζ := by
  have H : ∀ n : ℕ, ∀ θ : Field Γ, grainDeficit θ ζ = n →
      (∀ x, θ x ≤ ζ x) → Reach θ ζ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro θ hn hθ
      by_cases he : θ = ζ
      · subst θ
        exact Relation.ReflTransGen.refl
      · have hex : ∃ o : Γ, θ o < ζ o := by
          by_contra hno
          apply he
          funext x
          have hh := not_exists.mp hno x
          have hl := hθ x
          omega
        obtain ⟨o, ho⟩ := hex
        have hstep : ∀ x, addGrain θ o x ≤ ζ x := by
          intro x
          by_cases hx : x = o
          · subst x
            simp only [addGrain, Function.update_self]
            omega
          · simpa only [addGrain, Function.update_of_ne hx] using hθ x
        have hd : grainDeficit (addGrain θ o) ζ < grainDeficit θ ζ := by
          unfold grainDeficit
          apply Finset.sum_lt_sum
          · intro x _
            by_cases hx : x = o
            · subst x
              simp only [addGrain, Function.update_self]
              omega
            · simp only [addGrain, Function.update_of_ne hx, le_refl]
          · refine ⟨o, Finset.mem_univ _, ?_⟩
            simp only [addGrain, Function.update_self]
            omega
        exact (Relation.ReflTransGen.single (Step.grain θ o)).trans
          (ih (grainDeficit (addGrain θ o) ζ) (by omega) (addGrain θ o) rfl hstep)
  exact H _ η rfl hle

theorem reach_fill_negative {Γ : Finset Site2} (η : Field Γ) :
    Reach η (fun x => max (η x) 0) :=
  reach_of_le η _ (fun x => le_max_left (η x) 0)

/-- Every actual source legal list is transferred, including its order and all repeats. -/
theorem legal_list_reach {Γ : Finset Site2} (s : Site2 → ℤ) (w : List Site2)
    (hw : LegalList s w) (hΓ : ∀ x ∈ w, x ∈ Γ) :
    Reach (fun x : Γ => s x.val) (fun x : Γ => heightAfter s w x.val) := by
  let f (k : ℕ) : Field Γ := fun x => s x.val + lap (prefixCounts w k) x.val
  have H : ∀ k, k ≤ w.length → Reach (fun x : Γ => s x.val) (f k) := by
    intro k
    induction k with
    | zero =>
      intro _
      have he : f 0 = fun x : Γ => s x.val := by
        funext x
        simp only [f, prefix_zero, lap, nbrSumZ, Pi.zero_apply,
          Finset.sum_const_zero, mul_zero, sub_zero, add_zero]
      rw [he]
    | succ k ih =>
      intro hk
      have hkw : k < w.length := by omega
      let o : Γ := ⟨w[k], hΓ _ (List.getElem_mem hkw)⟩
      have hu : 4 ≤ f k o := hw k hkw
      have he : topple (f k) o = f (k + 1) := by
        funext x
        exact (height_succ s w k hkw x.val).symm
      rw [← he]
      exact (ih (by omega)).tail (Step.fire _ o hu)
  have h := H w.length le_rfl
  simpa only [f, prefix_eq_terminal w w.length le_rfl, heightAfter] using h

end
end FiniteAvalanches.Sandpile.RawInteger
