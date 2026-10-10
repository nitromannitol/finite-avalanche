import FiniteAvalanches.Needle.Sharp.SquareEnergy
import FiniteAvalanches.Needle.Sharp.Path
import FiniteAvalanches.Needle.Sharp.Subadditivity

set_option autoImplicit false
namespace Needle107Runs
open LatticeProb FiniteAvalanches.Needle FiniteAvalanches.Sandpile.FiniteWired
open Needle107SquareEnergy Needle107Path Needle107Subadditivity
open scoped BigOperators Classical

noncomputable def roots (h L : ℕ) (p : InBoxVertices h L)
    (T : Finset (Fin (L+1))) : Finset (Active (2*h)) :=
  Finset.univ.filter fun x => ∃ t ∈ T, site x = p.val t

lemma roots_empty (h L : ℕ) (p : InBoxVertices h L) : roots h L p ∅ = ∅ := by
  ext x
  simp only [roots, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
    false_and, exists_false]

lemma roots_card_le (h L : ℕ) (p : InBoxVertices h L) (T : Finset (Fin (L+1))) :
    (roots h L p T).card ≤ T.card := by
  let q (t : Fin (L+1)) : Active (2*h) :=
    activeOfSite (2*h) (p.val t) ((inBox_iff _ _).mpr (p.property t))
  have he : roots h L p T = T.image q := by
    ext x
    simp only [roots, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨t, ht, he⟩
      exact ⟨t, ht, site_injective _ he.symm⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, rfl⟩
  rw [he]
  exact Finset.card_image_le

lemma card_of_index_span (L n : ℕ) (T : Finset (Fin (L+1)))
    (hspan : ∀ s ∈ T, ∀ t ∈ T, |(s.val : ℤ)-t.val| ≤ n) : T.card ≤ n+1 := by
  by_cases hn : T.Nonempty
  · let a := T.min' hn
    have ha : a ∈ T := Finset.min'_mem T hn
    have hlo (t : Fin (L+1)) (ht : t ∈ T) : a.val ≤ t.val :=
      Finset.min'_le T t ht
    have hsub : T.image Fin.val ⊆ Finset.Icc a.val (a.val+n) := by
      rintro j hj
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hj
      have hh := hspan a ha t ht
      rw [abs_of_nonpos (by have := hlo t ht; omega)] at hh
      apply Finset.mem_Icc.mpr
      constructor
      · exact hlo t ht
      · omega
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Fin.val_injective, Nat.card_Icc] at hc
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty]
    exact Nat.zero_le _

noncomputable def bucket (L r : ℕ) (a : Fin (L+1))
    (T : Finset (Fin (L+1))) (j : Fin 4) : Finset (Fin (L+1)) :=
  T.filter fun t => (t.val-a.val)/r = j.val

/-- Four runs suffice for a layer whose index diameter is at most `4r-1`. -/
theorem roots_run_budget (h L r : ℕ) (hr : 1 ≤ r) (p : InBoxVertices h L)
    (hstep : ∀ t : Fin L, (lattice 2).Adj (p.val ⟨t.val, by omega⟩)
      (p.val ⟨t.val+1, by omega⟩)) (T : Finset (Fin (L+1)))
    (hspan : ∀ s ∈ T, ∀ t ∈ T, |(s.val : ℤ)-t.val| ≤ 4*r-1)
    (hdepth : ∀ t ∈ T, radius (p.val t)+2*r ≤ 2*h) :
    wiredConductance (2*h) (roots h L p T) ≤ 64 := by
  by_cases hn : T.Nonempty
  · let a := T.min' hn
    have ha : a ∈ T := Finset.min'_mem T hn
    have hlo (t : Fin (L+1)) (ht : t ∈ T) : a.val ≤ t.val := Finset.min'_le T t ht
    have hb (t : Fin (L+1)) (ht : t ∈ T) : (t.val-a.val)/r < 4 := by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0 < r)).mpr
      have hh := hspan a ha t ht
      have hlow := hlo t ht
      rw [abs_of_nonpos (by omega : (a.val : ℤ)-t.val ≤ 0)] at hh
      omega
    have he : roots h L p T = Finset.univ.biUnion
        (fun j : Fin 4 => roots h L p (bucket L r a T j)) := by
      ext x
      simp only [roots, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      constructor
      · rintro ⟨t, ht, hx⟩
        exact ⟨⟨(t.val-a.val)/r, hb t ht⟩, t,
          Finset.mem_filter.mpr ⟨ht, rfl⟩, hx⟩
      · rintro ⟨j, t, ht, hx⟩
        exact ⟨t, (Finset.mem_filter.mp ht).1, hx⟩
    have hcap (j : Fin 4) : wiredConductance (2*h) (roots h L p (bucket L r a T j)) ≤ 16 := by
      by_cases hj : (bucket L r a T j).Nonempty
      · let cidx := (bucket L r a T j).min' hj
        have hcm : cidx ∈ bucket L r a T j := Finset.min'_mem _ hj
        have hcT : cidx ∈ T := (Finset.mem_filter.mp hcm).1
        refine inner_square_conductance_le (2*h) r hr (p.val cidx)
          (by have := hdepth cidx hcT; omega) _ ?_
        intro x hx
        obtain ⟨t, ht, hxt⟩ := (Finset.mem_filter.mp hx).2
        have htT : t ∈ T := (Finset.mem_filter.mp ht).1
        have hci := (Finset.mem_filter.mp hcm).2
        have hti := (Finset.mem_filter.mp ht).2
        have h1 := Nat.div_add_mod (t.val-a.val) r
        have h2 := Nat.div_add_mod (cidx.val-a.val) r
        have h3 := Nat.mod_lt (t.val-a.val) (by omega : 0 < r)
        have h4 := Nat.mod_lt (cidx.val-a.val) (by omega : 0 < r)
        have hl1 := hlo t htT
        have hl2 := hlo cidx hcT
        have hsp : |(t.val : ℤ)-cidx.val| ≤ r := by
          rw [abs_le]
          rw [hti] at h1
          rw [hci] at h2
          omega
        rw [hxt]
        exact (path_linf_le_span L p.val hstep t cidx).trans hsp
      · rw [Finset.not_nonempty_iff_eq_empty.mp hj, roots_empty, wiredConductance_empty]
        norm_num
    rw [he]
    calc _ ≤ ∑ j : Fin 4, wiredConductance (2*h) (roots h L p (bucket L r a T j)) :=
            wiredConductance_biUnion_le (2*h) Finset.univ _
         _ ≤ ∑ _j : Fin 4, (16 : ℝ) := Finset.sum_le_sum fun j _ => hcap j
         _ = 64 := by norm_num
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn, roots_empty, wiredConductance_empty]
    norm_num

end Needle107Runs
