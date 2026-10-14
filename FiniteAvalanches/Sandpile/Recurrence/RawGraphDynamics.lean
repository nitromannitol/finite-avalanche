import FiniteAvalanches.Sandpile.Recurrence.RawGraphCarrier

/-! Actual grains and legal topplings on raw integer fields. Every parallel edge
is counted independently and the sink is never a firing site. -/
namespace FiniteAvalanches.Sandpile.RawGraph
open FiniteAvalanches.Sandpile
open scoped Classical BigOperators
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : FiniteAvalanches.Trees.Multigraph V E) (s : V)

/-- Number of original copies between two vertices. -/
def copies (x y : V) : ℕ := Burning.degreeInto G {y} x

theorem copies_self (x : V) : copies G x x = 0 := Burning.degree_into_self G x

theorem copies_symm (x y : V) : copies G x y = copies G y x := by
  unfold copies Burning.degreeInto
  congr 1
  ext e
  simp only [Burning.incidentInto, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  tauto

theorem degree_into_eq_sum (A : Finset V) (x : V) :
    Burning.degreeInto G A x = ∑ y ∈ A, copies G x y := by
  induction A using Finset.induction_on with
  | empty => simp [Burning.degreeInto, Burning.incidentInto]
  | @insert y A hy ih =>
    have hd : Disjoint ({y} : Finset V) A := Finset.disjoint_singleton_left.mpr hy
    rw [← Finset.singleton_union, Burning.degree_into_union G hd, ih]
    simp [copies, hy]

theorem active_degree_eq_sum (A : Finset (Burning.SourceVertex s))
    (x : Burning.SourceVertex s) :
    Burning.activeDegree G (Finset.univ.erase s) A x = ∑ y ∈ A, copies G x.val y.val := by
  rw [Burning.activeDegree, degree_into_eq_sum]
  exact Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)

theorem active_degree_erase (A : Finset (Burning.SourceVertex s))
    (o x : Burning.SourceVertex s) (ho : o ∈ A) :
    Burning.activeDegree G (Finset.univ.erase s) A x =
      Burning.activeDegree G (Finset.univ.erase s) (A.erase o) x + copies G x.val o.val := by
  rw [active_degree_eq_sum, active_degree_eq_sum]
  exact (Finset.sum_erase_add _ _ ho).symm

def addGrain (η : Field s) (o : Burning.SourceVertex s) : Field s :=
  Function.update η o (η o + 1)

def topple (η : Field s) (o : Burning.SourceVertex s) : Field s := fun x =>
  if x = o then η x - (Burning.degree G o.val : ℤ)
  else η x + (copies G x.val o.val : ℤ)

inductive Step : Field s → Field s → Prop
  | grain (η : Field s) (o : Burning.SourceVertex s) : Step η (addGrain s η o)
  | fire (η : Field s) (o : Burning.SourceVertex s)
      (hu : (Burning.degree G o.val : ℤ) ≤ η o) : Step η (topple G s η o)

abbrev Reach := Relation.ReflTransGen (Step G s)
def Accessible (η : Field s) : Prop := ∀ θ : Field s, Reach G s θ η

theorem no_fsc_iff (η : Field s) : NoFSC G s η ↔
    ∀ A : Finset (Burning.SourceVertex s), A.Nonempty →
      ∃ x ∈ A, (Burning.activeDegree G (Finset.univ.erase s) A x : ℤ) ≤ η x := by
  unfold NoFSC
  simp only [not_and, not_forall, not_lt, exists_prop]

theorem step_preserves_no_fsc {η ζ : Field s} (hn : NoFSC G s η)
    (h : Step G s η ζ) : NoFSC G s ζ := by
  apply (no_fsc_iff G s ζ).mpr
  intro A hA
  cases h with
  | grain o =>
    obtain ⟨x, hx, hη⟩ := (no_fsc_iff G s η).mp hn A hA
    refine ⟨x, hx, ?_⟩
    by_cases he : x = o
    · subst x; simp only [addGrain, Function.update_self]; omega
    · simpa only [addGrain, Function.update_of_ne he] using hη
  | fire o hu =>
    by_cases ho : o ∈ A
    · by_cases he : (A.erase o).Nonempty
      · obtain ⟨x, hx, hη⟩ := (no_fsc_iff G s η).mp hn (A.erase o) he
        have hxo := (Finset.mem_erase.mp hx).1
        refine ⟨x, (Finset.mem_erase.mp hx).2, ?_⟩
        rw [topple, if_neg hxo, active_degree_erase G s A o x ho, Nat.cast_add]
        omega
      · have hAs : A = {o} := by
          ext x
          simp only [Finset.mem_singleton]
          constructor
          · intro hx
            by_contra hxo
            exact he ⟨x, Finset.mem_erase.mpr ⟨hxo, hx⟩⟩
          · intro hx; subst x; exact ho
        refine ⟨o, ho, ?_⟩
        rw [hAs]
        simp only [Burning.activeDegree, Finset.image_singleton, Burning.degree_into_self,
          Nat.cast_zero, topple]
        omega
    · obtain ⟨x, hx, hη⟩ := (no_fsc_iff G s η).mp hn A hA
      have hxo : x ≠ o := fun he => ho (he ▸ hx)
      refine ⟨x, hx, ?_⟩
      rw [topple, if_neg hxo]
      have hc : (0 : ℤ) ≤ copies G x.val o.val := Nat.cast_nonneg _
      omega

theorem reach_preserves_no_fsc {η ζ : Field s} (hn : NoFSC G s η)
    (h : Reach G s η ζ) : NoFSC G s ζ := by
  induction h with
  | refl => exact hn
  | tail _ h ih => exact step_preserves_no_fsc G s ih h

private def grainDeficit (η ζ : Field s) : ℕ := ∑ x, (ζ x - η x).toNat

theorem reach_of_le (η ζ : Field s) (hle : ∀ x, η x ≤ ζ x) : Reach G s η ζ := by
  have H : ∀ n : ℕ, ∀ θ : Field s, grainDeficit s θ ζ = n →
      (∀ x, θ x ≤ ζ x) → Reach G s θ ζ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro θ hn hθ
      by_cases he : θ = ζ
      · subst θ; exact Relation.ReflTransGen.refl
      · have hex : ∃ o, θ o < ζ o := by
          by_contra hno
          apply he
          funext x
          have hh := not_exists.mp hno x
          have hl := hθ x
          omega
        obtain ⟨o, ho⟩ := hex
        have hs : ∀ x, addGrain s θ o x ≤ ζ x := by
          intro x
          by_cases hx : x = o
          · subst x; simp only [addGrain, Function.update_self]; omega
          · simpa only [addGrain, Function.update_of_ne hx] using hθ x
        have hd : grainDeficit s (addGrain s θ o) ζ < grainDeficit s θ ζ := by
          unfold grainDeficit
          apply Finset.sum_lt_sum
          · intro x _
            by_cases hx : x = o
            · subst x; simp only [addGrain, Function.update_self]; omega
            · simp only [addGrain, Function.update_of_ne hx, le_refl]
          · refine ⟨o, Finset.mem_univ _, ?_⟩
            simp only [addGrain, Function.update_self]
            omega
        exact (Relation.ReflTransGen.single (Step.grain θ o)).trans
          (ih _ (by omega) _ rfl hs)
  exact H _ η rfl hle

end
end FiniteAvalanches.Sandpile.RawGraph
