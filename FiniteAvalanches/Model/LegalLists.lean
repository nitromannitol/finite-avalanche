import LatticeProb.Sandpile.LeastAction

/-!
# Finite legal toppling lists

The definitions use the literal lattice toppling rule. Least action gives
uniqueness of the counts in a finite legal stabilization and finite determination
under agreement on the affected vertices and their neighbors.

These are deterministic ingredients for `th:main` and `dy:finite-determination`
in the manuscript, rather than statements of those probability theorems.
-/

namespace FiniteAvalanches.Sandpile

open LatticeProb LatticeProb.Sandpile

abbrev Site2 := Site 2
abbrev StableField := Site2 → Fin 4
abbrev Counts := Site2 →₀ ℕ

def initial (η : StableField) (ξ : Counts) (x : Site2) : ℤ :=
  (η x).val + (ξ x : ℤ)

noncomputable def listCounts (w : List Site2) : Counts :=
  (w : Multiset Site2).toFinsupp

theorem listCounts_apply (w : List Site2) (x : Site2) :
    listCounts w x = w.count x := by
  simp [listCounts]

theorem listCounts_support (w : List Site2) :
    (listCounts w).support = w.toFinset := rfl

theorem listCounts_total (w : List Site2) :
    (listCounts w).sum (fun _ n => n) = w.length := by
  simp [listCounts, Finsupp.sum]

def prefixCounts (w : List Site2) (k : ℕ) (x : Site2) : ℤ :=
  ((w.take k).count x : ℤ)

def LegalList (s : Site2 → ℤ) (w : List Site2) : Prop :=
  ∀ (k : ℕ) (hk : k < w.length), 4 ≤ s w[k] + lap (prefixCounts w k) w[k]

def Stabilizes (η : StableField) (ξ : Counts) (w : List Site2) : Prop :=
  LegalList (initial η ξ) w ∧
    ∀ x, 0 ≤ initial η ξ x + lap (fun y => (listCounts w y : ℤ)) x ∧
      initial η ξ x + lap (fun y => (listCounts w y : ℤ)) x < 4

theorem prefix_zero (w : List Site2) : prefixCounts w 0 = 0 := by
  funext x
  simp [prefixCounts]

theorem prefix_succ (w : List Site2) (k : ℕ) (hk : k < w.length) (x : Site2) :
    prefixCounts w (k + 1) x = prefixCounts w k x + if x = w[k] then 1 else 0 := by
  unfold prefixCounts
  rw [List.take_succ_eq_append_getElem hk, List.count_append]
  by_cases hx : x = w[k]
  · simp [hx]
  · simp [hx, Ne.symm hx]

theorem prefix_eq_terminal (w : List Site2) (k : ℕ) (hk : w.length ≤ k) :
    prefixCounts w k = fun x => (listCounts w x : ℤ) := by
  funext x
  simp [prefixCounts, List.take_of_length_le hk, listCounts_apply]

theorem prefix_succ_eq (w : List Site2) (k : ℕ) (hk : k < w.length) :
    prefixCounts w (k + 1) = fun x => prefixCounts w k x + dirac w[k] x := by
  funext x
  simpa only [dirac] using prefix_succ w k hk x

theorem lap_add (u v : Site2 → ℤ) (x : Site2) :
    lap (fun y => u y + v y) x = lap u x + lap v x := by
  simp only [lap, nbrSumZ, Fin.sum_univ_two]
  ring

theorem height_succ (s : Site2 → ℤ) (w : List Site2) (k : ℕ)
    (hk : k < w.length) (x : Site2) :
    s x + lap (prefixCounts w (k + 1)) x =
      s x + lap (prefixCounts w k) x + lap (dirac w[k]) x := by
  rw [prefix_succ_eq w k hk, lap_add]
  ring

theorem dirac_nonneg (z x : Site2) : 0 ≤ dirac z x := by
  simp only [dirac]
  split <;> norm_num

theorem lap_dirac_self (z : Site2) : lap (dirac z) z = -4 := by
  have hp (i : Fin 2) : dirac z (z + unit i) = 0 := by
    apply dirac_of_ne
    intro h
    have hi := congrFun h i
    simp [unit] at hi
  have hm (i : Fin 2) : dirac z (z - unit i) = 0 := by
    apply dirac_of_ne
    intro h
    have hi := congrFun h i
    simp [unit] at hi
  simp [lap, nbrSumZ, hp, hm]

theorem lap_dirac_nonneg {z x : Site2} (hx : x ≠ z) : 0 ≤ lap (dirac z) x := by
  rw [lap, dirac_of_ne hx]
  simp only [mul_zero, sub_zero]
  apply Finset.sum_nonneg
  intro i _
  exact add_nonneg (dirac_nonneg z _) (dirac_nonneg z _)

theorem LegalList.heights_nonneg {s : Site2 → ℤ} {w : List Site2}
    (h : LegalList s w) (hs : ∀ x, 0 ≤ s x) :
    ∀ k x, 0 ≤ s x + lap (prefixCounts w k) x := by
  intro k
  induction k with
  | zero =>
    intro x
    simpa [prefix_zero, lap, nbrSumZ] using hs x
  | succ k ih =>
    intro x
    by_cases hk : k < w.length
    · rw [height_succ s w k hk x]
      by_cases hx : x = w[k]
      · subst x
        rw [lap_dirac_self]
        have ht := h k hk
        omega
      · exact add_nonneg (ih x) (lap_dirac_nonneg hx)
    · have he : prefixCounts w (k + 1) = prefixCounts w k := by
        rw [prefix_eq_terminal w (k + 1) (by omega),
          prefix_eq_terminal w k (by omega)]
      rw [he]
      exact ih x

theorem LegalList.isLegalToppling {s : Site2 → ℤ} {w : List Site2}
    (h : LegalList s w) : IsLegalToppling s (prefixCounts w) := by
  refine ⟨prefix_zero w, ?_⟩
  intro k x
  by_cases hk : k < w.length
  · rw [prefix_succ w k hk x]
    by_cases hx : x = w[k]
    · right
      subst x
      exact ⟨by simp, by simpa using h k hk⟩
    · left
      simp [hx]
  · left
    rw [prefix_eq_terminal w (k + 1) (by omega),
      prefix_eq_terminal w k (by omega)]

theorem initial_nonneg (η : StableField) (ξ : Counts) (x : Site2) :
    0 ≤ initial η ξ x := by
  dsimp [initial]
  positivity

theorem stabilizes_iff_legal_and_lt (η : StableField) (ξ : Counts) (w : List Site2) :
    Stabilizes η ξ w ↔ LegalList (initial η ξ) w ∧
      ∀ x, initial η ξ x + lap (fun y => (listCounts w y : ℤ)) x < 4 := by
  constructor
  · exact fun h => ⟨h.1, fun x => (h.2 x).2⟩
  · rintro ⟨h, hs⟩
    refine ⟨h, fun x => ⟨?_, hs x⟩⟩
    have hn := h.heights_nonneg (initial_nonneg η ξ) w.length x
    rw [prefix_eq_terminal w w.length le_rfl] at hn
    exact hn

theorem stabilizes_nil_zero (η : StableField) : Stabilizes η 0 [] := by
  rw [stabilizes_iff_legal_and_lt]
  constructor
  · intro k hk
    simp at hk
  · intro x
    simp [initial, listCounts, lap, nbrSumZ]

theorem legalList_le {s : Site2 → ℤ} {w : List Site2} (h : LegalList s w)
    (v : Counts) (hv : ∀ x, s x + lap (fun y => (v y : ℤ)) x < 4) :
    ∀ x, listCounts w x ≤ v x := by
  intro x
  have hb := le_of_isLegalToppling h.isLegalToppling
    (w := fun y => (v y : ℤ)) (fun y => by positivity)
    (by simpa using hv) w.length x
  rw [prefix_eq_terminal w w.length le_rfl] at hb
  change (listCounts w x : ℤ) ≤ (v x : ℤ) at hb
  exact_mod_cast hb

theorem stabilizes_counts_unique {η : StableField} {ξ : Counts} {w v : List Site2}
    (hw : Stabilizes η ξ w) (hv : Stabilizes η ξ v) : listCounts w = listCounts v := by
  apply Finsupp.ext
  intro x
  exact le_antisymm (legalList_le hw.1 (listCounts v) (fun y => (hv.2 y).2) x)
    (legalList_le hv.1 (listCounts w) (fun y => (hw.2 y).2) x)

theorem existsUnique_counts {η : StableField} {ξ : Counts}
    (h : ∃ w, Stabilizes η ξ w) :
    ∃! u : Counts, ∃ w, Stabilizes η ξ w ∧ listCounts w = u := by
  obtain ⟨w, hw⟩ := h
  refine ⟨listCounts w, ⟨w, hw, rfl⟩, ?_⟩
  rintro u ⟨v, hv, rfl⟩
  exact stabilizes_counts_unique hv hw

def StabilizationDomain (ξ : Counts) := {η : StableField // ∃ w, Stabilizes η ξ w}

noncomputable def odometer (ξ : Counts) (η : StabilizationDomain ξ) : Counts :=
  Classical.choose (existsUnique_counts η.property)

theorem odometer_spec (ξ : Counts) (η : StabilizationDomain ξ) :
    ∃ w, Stabilizes η.val ξ w ∧ listCounts w = odometer ξ η :=
  (Classical.choose_spec (existsUnique_counts η.property)).1

theorem odometer_eq_counts (ξ : Counts) (η : StabilizationDomain ξ)
    {w : List Site2} (hw : Stabilizes η.val ξ w) : odometer ξ η = listCounts w := by
  obtain ⟨v, hv, he⟩ := odometer_spec ξ η
  exact he.symm.trans (stabilizes_counts_unique hv hw)

theorem odometer_final_stable (ξ : Counts) (η : StabilizationDomain ξ) (x : Site2) :
    0 ≤ initial η.val ξ x + lap (fun y => (odometer ξ η y : ℤ)) x ∧
      initial η.val ξ x + lap (fun y => (odometer ξ η y : ℤ)) x < 4 := by
  obtain ⟨w, hw, he⟩ := odometer_spec ξ η
  rw [← he]
  exact hw.2 x

noncomputable def addition (ξ : Counts) (η : StabilizationDomain ξ) : StableField :=
  fun x => ⟨(initial η.val ξ x + lap (fun y => (odometer ξ η y : ℤ)) x).toNat,
    (Int.toNat_lt (odometer_final_stable ξ η x).1).mpr
      (odometer_final_stable ξ η x).2⟩

theorem addition_eq (ξ : Counts) (η : StabilizationDomain ξ) (x : Site2) :
    ((addition ξ η x).val : ℤ) =
      initial η.val ξ x + lap (fun y => (odometer ξ η y : ℤ)) x :=
  Int.toNat_of_nonneg (odometer_final_stable ξ η x).1

def affected (ξ u : Counts) : Finset Site2 :=
  ξ.support ∪ u.support ∪ u.support.biUnion nbrFinset

theorem mem_nbrFinset_iff_adj (x y : Site2) :
    y ∈ nbrFinset x ↔ (lattice 2).Adj x y := by
  change y ∈ nbrFinset x ↔ ∃ i : Fin 2, y = x + unit i ∨ x = y + unit i
  simp only [nbrFinset, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi | hi⟩
    · exact ⟨i, Or.inl hi⟩
    · exact ⟨i, Or.inr (by rw [hi]; abel)⟩
  · rintro ⟨i, hi | hi⟩
    · exact ⟨i, Or.inl hi⟩
    · exact ⟨i, Or.inr (by rw [hi]; abel)⟩

theorem mem_affected_iff (ξ u : Counts) (x : Site2) :
    x ∈ affected ξ u ↔ ξ x ≠ 0 ∨ u x ≠ 0 ∨
      ∃ y, u y ≠ 0 ∧ (lattice 2).Adj y x := by
  simp only [affected, Finset.mem_union, Finset.mem_biUnion, Finsupp.mem_support_iff,
    mem_nbrFinset_iff_adj, or_assoc]

theorem mem_affected_of_list {ξ : Counts} {w : List Site2} {x : Site2}
    (hx : x ∈ w) : x ∈ affected ξ (listCounts w) := by
  simp only [affected, listCounts_support, Finset.mem_union, List.mem_toFinset]
  exact Or.inl (Or.inr hx)

theorem count_zero_outside_affected {ξ u : Counts} {x : Site2}
    (hx : x ∉ affected ξ u) : ξ x = 0 ∧ u x = 0 := by
  simp only [affected, Finset.mem_union, not_or] at hx
  exact ⟨Finsupp.notMem_support_iff.mp hx.1.1,
    Finsupp.notMem_support_iff.mp hx.1.2⟩

theorem lap_zero_outside_affected {ξ u : Counts} {x : Site2}
    (hx : x ∉ affected ξ u) : lap (fun y => (u y : ℤ)) x = 0 := by
  have hux := (count_zero_outside_affected hx).2
  have hn : ∀ y ∈ nbrFinset x, u y = 0 := by
    intro y hy
    by_contra h
    apply hx
    simp only [affected, Finset.mem_union]
    right
    apply Finset.mem_biUnion.mpr
    refine ⟨y, Finsupp.mem_support_iff.mpr h, ?_⟩
    simp only [nbrFinset, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    obtain ⟨i, hi | hi⟩ := hy
    · exact ⟨i, Or.inr (by rw [hi]; abel)⟩
    · exact ⟨i, Or.inl (by rw [hi]; abel)⟩
  have hp (i : Fin 2) : u (x + unit i) = 0 :=
    hn _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp⟩)
  have hm (i : Fin 2) : u (x - unit i) = 0 :=
    hn _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp⟩)
  simp [lap, nbrSumZ, hux, hp, hm]

theorem stabilizes_transfer {η η' : StableField} {ξ : Counts} {w : List Site2}
    (hw : Stabilizes η ξ w)
    (heq : ∀ x ∈ affected ξ (listCounts w), η' x = η x) :
    Stabilizes η' ξ w := by
  constructor
  · intro k hk
    have hx : w[k] ∈ affected ξ (listCounts w) :=
      mem_affected_of_list (List.getElem_mem hk)
    simpa [initial, heq _ hx] using hw.1 k hk
  · intro x
    by_cases hx : x ∈ affected ξ (listCounts w)
    · simpa [initial, heq x hx] using hw.2 x
    · have hz := count_zero_outside_affected hx
      rw [lap_zero_outside_affected hx]
      simp only [initial, hz.1, Nat.cast_zero, add_zero]
      exact ⟨by positivity, by exact_mod_cast (η' x).isLt⟩

theorem stabilizes_iff_of_agree {η η' : StableField} {ξ : Counts} {w : List Site2}
    (heq : ∀ x ∈ affected ξ (listCounts w), η' x = η x) :
    Stabilizes η' ξ w ↔ Stabilizes η ξ w :=
  ⟨fun h => stabilizes_transfer h (fun x hx => (heq x hx).symm),
    fun h => stabilizes_transfer h heq⟩

def WiredStabilizes (η : StableField) (ξ : Counts) (V : Finset Site2)
    (w : List Site2) : Prop :=
  (∀ x ∈ w, x ∈ V) ∧ LegalList (initial η ξ) w ∧
    ∀ x ∈ V, 0 ≤ initial η ξ x + lap (fun y => (listCounts w y : ℤ)) x ∧
      initial η ξ x + lap (fun y => (listCounts w y : ℤ)) x < 4

theorem stabilizes_transfer_wired {η η' : StableField} {ξ : Counts} {w : List Site2}
    (hw : Stabilizes η ξ w)
    (heq : ∀ x ∈ affected ξ (listCounts w), η' x = η x)
    (V : Finset Site2) (hV : affected ξ (listCounts w) ⊆ V) :
    WiredStabilizes η' ξ V w := by
  have ht := stabilizes_transfer hw heq
  exact ⟨fun x hx => hV (mem_affected_of_list hx), ht.1, fun x _ => ht.2 x⟩

theorem prefix_zero_of_not_mem {w : List Site2} {x : Site2} (hx : x ∉ w) (k : ℕ) :
    prefixCounts w k x = 0 := by
  simp only [prefixCounts, Nat.cast_eq_zero]
  exact List.count_eq_zero_of_not_mem (fun h => hx (List.mem_of_mem_take h))

theorem wired_legalList_le {s : Site2 → ℤ} {w : List Site2} (h : LegalList s w)
    (V : Finset Site2) (hwV : ∀ x ∈ w, x ∈ V)
    (v : Counts) (hv : ∀ x ∈ V, s x + lap (fun y => (v y : ℤ)) x < 4) :
    ∀ k x, prefixCounts w k x ≤ (v x : ℤ) := by
  intro k
  induction k with
  | zero => intro x; rw [prefix_zero]; exact Nat.cast_nonneg _
  | succ k ih =>
    intro x
    rcases h.isLegalToppling.2 k x with he | ⟨he, htop⟩
    · rw [he]; exact ih x
    · rw [he]
      have hxw : x ∈ w := by
        by_contra hxw
        have h0 := prefix_zero_of_not_mem hxw k
        have h1 := prefix_zero_of_not_mem hxw (k + 1)
        omega
      by_contra hlt
      have hx : prefixCounts w k x = (v x : ℤ) := le_antisymm (ih x) (by omega)
      have hl := lap_le_lap_of_le ih hx
      have hs := hv x (hwV x hxw)
      norm_num at htop
      omega

theorem wiredStabilizes_counts_unique {η : StableField} {ξ : Counts} {V : Finset Site2}
    {w v : List Site2} (hw : WiredStabilizes η ξ V w)
    (hv : WiredStabilizes η ξ V v) : listCounts w = listCounts v := by
  apply Finsupp.ext
  intro x
  have h1 := wired_legalList_le hw.2.1 V hw.1 (listCounts v)
    (fun y hy => (hv.2.2 y hy).2) w.length x
  have h2 := wired_legalList_le hv.2.1 V hv.1 (listCounts w)
    (fun y hy => (hw.2.2 y hy).2) v.length x
  rw [prefix_eq_terminal w w.length le_rfl] at h1
  rw [prefix_eq_terminal v v.length le_rfl] at h2
  change (listCounts w x : ℤ) ≤ (listCounts v x : ℤ) at h1
  change (listCounts v x : ℤ) ≤ (listCounts w x : ℤ) at h2
  exact_mod_cast le_antisymm h1 h2

theorem finite_determination_counts {η η' : StableField} {ξ : Counts} {w : List Site2}
    (hw : Stabilizes η ξ w)
    (heq : ∀ x ∈ affected ξ (listCounts w), η' x = η x) :
    (Stabilizes η' ξ w ∧
      ∀ v, Stabilizes η' ξ v → listCounts v = listCounts w) ∧
    ∀ V : Finset Site2, affected ξ (listCounts w) ⊆ V →
      WiredStabilizes η' ξ V w ∧
        ∀ v, WiredStabilizes η' ξ V v → listCounts v = listCounts w := by
  have ht := stabilizes_transfer hw heq
  refine ⟨⟨ht, fun _ hv => stabilizes_counts_unique hv ht⟩, ?_⟩
  intro V hV
  have htV := stabilizes_transfer_wired hw heq V hV
  exact ⟨htV, fun _ hv => wiredStabilizes_counts_unique hv htV⟩

theorem exists_domain_odometer_eq (ξ : Counts) (η : StabilizationDomain ξ)
    (η' : StableField)
    (heq : ∀ x ∈ affected ξ (odometer ξ η), η' x = η.val x) :
    ∃ ζ : StabilizationDomain ξ, ζ.val = η' ∧ odometer ξ ζ = odometer ξ η := by
  obtain ⟨w, hw, he⟩ := odometer_spec ξ η
  have ht : Stabilizes η' ξ w :=
    stabilizes_transfer hw (by simpa [he] using heq)
  refine ⟨⟨η', w, ht⟩, rfl, ?_⟩
  exact (odometer_eq_counts ξ ⟨η', w, ht⟩ ht).trans he


end FiniteAvalanches.Sandpile
