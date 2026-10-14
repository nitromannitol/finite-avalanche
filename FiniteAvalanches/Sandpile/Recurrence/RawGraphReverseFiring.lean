import FiniteAvalanches.Sandpile.Recurrence.RawGraphLaplacian

/-! At every nonzero remaining script, NoFSC supplies a legal firing in the
positive maximum layer. Strong induction on the total gives the ordered word. -/
namespace FiniteAvalanches.Sandpile.RawGraph
open FiniteAvalanches.Sandpile
open scoped Classical BigOperators
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : FiniteAvalanches.Trees.Multigraph V E) (s : V)

theorem exists_legal_maximum (η : Field s) (hη : NoFSC G s η)
    (n : V → ℕ) (hs : n s = 0) (hn : n ≠ fun _ => 0) :
    ∃ o : Burning.SourceVertex s, 0 < n o.val ∧
      (Burning.degree G o.val : ℤ) ≤ raised G s η n o := by
  obtain ⟨z, _, hz⟩ := Finset.exists_max_image (Finset.univ : Finset V) n
    ⟨s, Finset.mem_univ _⟩
  have hm : ∀ y, n y ≤ n z := fun y => hz y (Finset.mem_univ _)
  have hp : 0 < n z := by
    by_contra h
    apply hn
    funext y
    have hy := hm y
    omega
  have hzns : z ≠ s := by intro h; subst z; omega
  let zz : Burning.SourceVertex s := ⟨z, by simp [hzns]⟩
  let A : Finset (Burning.SourceVertex s) := Finset.univ.filter fun x => n x.val = n z
  have hA : A.Nonempty := ⟨zz, by simp [A, zz]⟩
  obtain ⟨x, hx, hheight⟩ := (no_fsc_iff G s η).mp hη A hA
  have hxm : n x.val = n z := (Finset.mem_filter.mp hx).2
  have hmem : ∀ y, y ∈ A.image Subtype.val ↔ n y = n z := by
    intro y
    constructor
    · intro hy
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hv).2
    · intro hy
      have hyns : y ≠ s := by intro he; subst y; omega
      refine Finset.mem_image.mpr ⟨⟨y, by simp [hyns]⟩, ?_, rfl⟩
      simp [A, hy]
  have hbound : (Burning.degreeInto G (Finset.univ \ A.image Subtype.val) x.val : ℤ) ≤
      lapInt G (fun y => n y) x.val := by
    rw [degree_into_eq_sum G, Nat.cast_sum]
    have he : (∑ y ∈ Finset.univ \ A.image Subtype.val, (copies G x.val y : ℤ)) =
        ∑ y, if y ∈ A.image Subtype.val then 0 else (copies G x.val y : ℤ) := by
      simp only [Finset.sdiff_eq_filter, Finset.sum_filter, ite_not]
    rw [he]
    unfold lapInt
    apply Finset.sum_le_sum
    intro y _
    dsimp only
    have hcy : (0 : ℤ) ≤ copies G x.val y := Nat.cast_nonneg _
    by_cases hy : y ∈ A.image Subtype.val
    · rw [if_pos hy]
      exact mul_nonneg hcy (sub_nonneg.mpr (by
        exact_mod_cast (hm y).trans_eq hxm.symm))
    · rw [if_neg hy]
      have hlt : n y < n x.val := by
        have ht := hm y
        have hne := mt ((hmem y).mpr) hy
        omega
      have hdiff : (1 : ℤ) ≤ (n x.val : ℤ) - n y := by omega
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hdiff hcy
  refine ⟨x, by omega, ?_⟩
  have hd := Burning.degree_into_compl G (A.image Subtype.val) x.val
  have hdZ : (Burning.degreeInto G (Finset.univ \ A.image Subtype.val) x.val : ℤ) +
      (Burning.activeDegree G (Finset.univ.erase s) A x : ℤ) =
      (Burning.degree G x.val : ℤ) := by
    change (Burning.degreeInto G _ x.val : ℤ) + (Burning.degreeInto G _ x.val : ℤ) = _
    exact_mod_cast hd
  change _ ≤ η x + lapInt G (fun y => n y) x.val
  omega

/-- NoFSC alone supplies the complete legal firing word for every sink-zero script. -/
theorem reverse_firing (η : Field s) (hη : NoFSC G s η)
    (n : V → ℕ) (hs : n s = 0) : Reach G s (raised G s η n) η := by
  have H : ∀ k : ℕ, ∀ m : V → ℕ, (∑ y, m y) = k → m s = 0 →
      Reach G s (raised G s η m) η := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro m hm hms
      by_cases he : m = fun _ => 0
      · subst m
        rw [raised_zero]
      · obtain ⟨o, ho, hu⟩ := exists_legal_maximum G s η hη m hms he
        let m' := Function.update m o.val (m o.val - 1)
        have hm's : m' s = 0 := by
          simp only [m', Function.update_of_ne (Ne.symm (Burning.source_vertex_ne_sink s o)), hms]
        have hlt : (∑ y, m' y) < ∑ y, m y := by
          apply Finset.sum_lt_sum
          · intro y _
            by_cases hy : y = o.val
            · subst y; simp only [m', Function.update_self]; omega
            · simp only [m', Function.update_of_ne hy, le_refl]
          · refine ⟨o.val, Finset.mem_univ _, ?_⟩
            simp only [m', Function.update_self]
            omega
        have hnext : Reach G s (raised G s η m) (raised G s η m') := by
          rw [← topple_raised_decrement G s η m o ho]
          exact Relation.ReflTransGen.single (Step.fire _ o hu)
        exact hnext.trans (ih _ (by omega) m' rfl hm's)
  exact H _ n rfl hs

end
end FiniteAvalanches.Sandpile.RawGraph
