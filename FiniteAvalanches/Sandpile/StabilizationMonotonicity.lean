import FiniteAvalanches.Sandpile.Sequential

set_option autoImplicit false
namespace FiniteAvalanches.Sandpile
open LatticeProb LatticeProb.Sandpile FiniteAvalanches FiniteAvalanches.Sandpile.Waves
open scoped Classical
noncomputable section

/-- More grains never lower the initial heights. -/
theorem initial_le_initial_add (η : StableField) (ξ ζ : Counts) (x : Site2) :
    initial η ξ x ≤ initial η (ξ + ζ) x := by
  have hz : (0 : ℤ) ≤ (ζ x : ℤ) := Nat.cast_nonneg _
  simp only [initial, Finsupp.add_apply, Nat.cast_add]
  linarith

/-- A legal list stays legal when the initial heights increase. -/
theorem legalList_mono {s t : Site2 → ℤ} {w : List Site2} (h : LegalList s w)
    (hst : ∀ x, s x ≤ t x) : LegalList t w := by
  intro k hk
  have h1 := h k hk
  have h2 := hst (w[k]'hk)
  omega

/-- Least action: a legal list is no longer than any stabilizing list. -/
theorem legalList_length_le_of_stable {s : Site2 → ℤ} {p w : List Site2}
    (hp : LegalList s p) (hw : ∀ x, s x + lap (fun y => (listCounts w y : ℤ)) x < 4) :
    p.length ≤ w.length := by
  have hb : ∀ x, listCounts p x ≤ listCounts w x := legalList_le hp (listCounts w) hw
  rw [← listCounts_total p, ← listCounts_total w]
  exact Finsupp.sum_le_sum_index hb (fun _ _ => monotone_id) (fun _ _ => rfl)

/-- Bounded legal lists give a finite legal stabilization: take a longest one. -/
theorem exists_stabilizes_of_legal_length_le (η : StableField) (ξ : Counts) (B : ℕ)
    (hB : ∀ p : List Site2, LegalList (initial η ξ) p → p.length ≤ B) :
    ∃ w, Stabilizes η ξ w := by
  let P (n : ℕ) := ∃ p : List Site2, p.length = n ∧ LegalList (initial η ξ) p
  have h0 : P 0 := ⟨[], rfl, by intro k hk; simp at hk⟩
  obtain ⟨w, hwlen, hw⟩ := Nat.findGreatest_spec (P := P) (Nat.zero_le B) h0
  refine ⟨w, (stabilizes_iff_legal_and_lt η ξ w).mpr ⟨hw, ?_⟩⟩
  intro x
  by_contra hn
  have hw' := legal_list_append_singleton hw x (by omega)
  have hb := hB _ hw'
  have hp : P (w ++ [x]).length := ⟨w ++ [x], rfl, hw'⟩
  have hm := Nat.le_findGreatest (P := P) hb hp
  simp only [List.length_append, List.length_singleton] at hm
  omega

/-- Legality of a first stabilizing list followed by a legal list for the stabilized field. -/
theorem legalList_consecutive {η η' : StableField} {ξ ζ : Counts} {w v : List Site2}
    (hw : Stabilizes η ξ w)
    (he : ∀ x, heightAfter (initial η ξ) w x = ((η' x).val : ℤ))
    (hv : LegalList (initial η' ζ) v) : LegalList (initial η (ξ + ζ)) (w ++ v) := by
  have hstate (x : Site2) :
      heightAfter (initial η (ξ + ζ)) w x = initial η' ζ x := by
    have h := he x
    simp only [heightAfter, initial, Finsupp.add_apply, Nat.cast_add] at h ⊢
    linarith only [h]
  have hlw : LegalList (initial η (ξ + ζ)) w := by
    intro k hk
    have h := hw.1 k hk
    have hz : (0 : ℤ) ≤ ζ w[k] := Nat.cast_nonneg _
    simp only [initial, Finsupp.add_apply, Nat.cast_add] at h ⊢
    linarith only [h, hz]
  have hlv : LegalList (heightAfter (initial η (ξ + ζ)) w) v := by
    intro k hk
    rw [hstate]
    exact hv k hk
  exact legal_list_append hlw hlv

/-- A finite legal stabilization of `η + (ξ + ζ)` gives one for `η + ξ`. -/
theorem exists_stabilizes_of_add_left {η : StableField} {ξ ζ : Counts}
    (h : ∃ w, Stabilizes η (ξ + ζ) w) : ∃ w, Stabilizes η ξ w := by
  obtain ⟨t, ht⟩ := h
  refine exists_stabilizes_of_legal_length_le η ξ t.length (fun p hp => ?_)
  have hp' : LegalList (initial η (ξ + ζ)) p :=
    legalList_mono hp (initial_le_initial_add η ξ ζ)
  exact legalList_length_le_of_stable hp' (fun x => (ht.2 x).2)

/-- After the first addition stabilizes, the second stabilizes on its output. -/
theorem exists_stabilizes_after_of_add {η : StableField} {ξ ζ : Counts}
    (h : ∃ w, Stabilizes η (ξ + ζ) w) (hξ : ∃ w, Stabilizes η ξ w) :
    ∃ v, Stabilizes (addition ξ ⟨η, hξ⟩) ζ v := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨w, hw, he⟩ := odometer_spec ξ ⟨η, hξ⟩
  have hs (x : Site2) :
      heightAfter (initial η ξ) w x = ((addition ξ ⟨η, hξ⟩ x).val : ℤ) := by
    have h1 := addition_eq ξ ⟨η, hξ⟩ x
    rw [← he] at h1
    exact h1.symm
  refine exists_stabilizes_of_legal_length_le (addition ξ ⟨η, hξ⟩) ζ t.length
    (fun v hv => ?_)
  have hl := legalList_consecutive hw hs hv
  have hlen := legalList_length_le_of_stable hl (fun x => (ht.2 x).2)
  simp only [List.length_append] at hlen
  omega

/-- A total finite legal stabilization of `ξ + ζ` is equivalent to successive ones. -/
theorem stabilizes_add_iff (η : StableField) (ξ ζ : Counts) :
    (∃ w, Stabilizes η (ξ + ζ) w) ↔
      ∃ (h₁ : ∃ w, Stabilizes η ξ w), ∃ v, Stabilizes (addition ξ ⟨η, h₁⟩) ζ v := by
  constructor
  · intro h
    have h₁ := exists_stabilizes_of_add_left h
    exact ⟨h₁, exists_stabilizes_after_of_add h h₁⟩
  · rintro ⟨h₁, hv⟩
    exact exists_stabilization_add_of_sequential ξ ζ ⟨η, h₁⟩ hv

/-- One total stabilization gives both sequential orders. -/
theorem sequential_stabilizes_both_orders {η : StableField} {ξ ζ : Counts}
    (h : ∃ w, Stabilizes η (ξ + ζ) w) :
    ∃ (h₁ : ∃ w, Stabilizes η ξ w) (h₂ : ∃ w, Stabilizes η ζ w),
      (∃ v, Stabilizes (addition ξ ⟨η, h₁⟩) ζ v) ∧
        (∃ v, Stabilizes (addition ζ ⟨η, h₂⟩) ξ v) := by
  have h' : ∃ w, Stabilizes η (ζ + ξ) w := by
    rw [add_comm ζ ξ]
    exact h
  have h₁ := exists_stabilizes_of_add_left h
  have h₂ := exists_stabilizes_of_add_left h'
  exact ⟨h₁, h₂, exists_stabilizes_after_of_add h h₁, exists_stabilizes_after_of_add h' h₂⟩

#print axioms FiniteAvalanches.Sandpile.initial_le_initial_add
#print axioms FiniteAvalanches.Sandpile.legalList_mono
#print axioms FiniteAvalanches.Sandpile.legalList_length_le_of_stable
#print axioms FiniteAvalanches.Sandpile.exists_stabilizes_of_legal_length_le
#print axioms FiniteAvalanches.Sandpile.legalList_consecutive
#print axioms FiniteAvalanches.Sandpile.exists_stabilizes_of_add_left
#print axioms FiniteAvalanches.Sandpile.exists_stabilizes_after_of_add
#print axioms FiniteAvalanches.Sandpile.stabilizes_add_iff
#print axioms FiniteAvalanches.Sandpile.sequential_stabilizes_both_orders

end
end FiniteAvalanches.Sandpile
