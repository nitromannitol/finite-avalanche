import FiniteAvalanches.Sandpile.Waves.Uniqueness
import FiniteAvalanches.Model.FiniteWired

/-! The elementary forbidden-set argument precedes the inverse-wave map.
All degrees count the literal four lattice neighbors; wired exit copies are sink edges. -/

namespace FiniteAvalanches.Sandpile.Waves

open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

def degree (A : Finset Site2) (x : Site2) : ℕ := (nbrFinset x ∩ A).card

def forbidden (h : Site2 → ℤ) (A : Finset Site2) : Prop :=
  A.Nonempty ∧ ∀ x ∈ A, h x < (degree A x : ℤ)

def allowed (V : Finset Site2) (h : Site2 → ℤ) : Prop :=
  ∀ A ⊆ V, ¬forbidden h A

theorem not_mem_neighbors_self (x : Site2) : x ∉ nbrFinset x := by
  rw [FiniteWired.mem_neighbors_iff]
  exact (lattice 2).loopless.irrefl x

theorem sum_neighbors (f : Site2 → ℤ) (x : Site2) :
    ∑ y ∈ nbrFinset x, f y = nbrSumZ f x := by
  rw [nbrFinset, Finset.sum_biUnion]
  · have hn : ∀ i : Fin 2, x + unit i ≠ x - unit i := by
      intro i h
      have hi := congrFun h i
      simp only [unit, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same] at hi
      omega
    simp only [Finset.sum_pair (hn _), nbrSumZ]
  · intro i _ j _ hij
    simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    rintro a (rfl | rfl) (h | h) <;>
      have h1 := congrFun h i <;> have h2 := congrFun h j <;>
      simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne, hij] at h1 h2

theorem degree_eq_sum (A : Finset Site2) (x : Site2) :
    (degree A x : ℤ) = nbrSumZ (fun y => if y ∈ A then 1 else 0) x := by
  rw [← sum_neighbors]
  simp only [degree, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.sum_const, nsmul_eq_mul, mul_one, Finset.inter_comm]

theorem degree_mono {A B : Finset Site2} (h : A ⊆ B) (x : Site2) :
    degree A x ≤ degree B x := Finset.card_le_card (Finset.inter_subset_inter_left h)

theorem degree_erase (A : Finset Site2) (o x : Site2) :
    (degree A x : ℤ) = (degree (A.erase o) x : ℤ) +
      if o ∈ A ∧ o ∈ nbrFinset x then 1 else 0 := by
  unfold degree
  have he : nbrFinset x ∩ A.erase o = (nbrFinset x ∩ A).erase o := by ext; simp; tauto
  rw [he]
  by_cases ho : o ∈ nbrFinset x ∩ A
  · rw [Finset.card_erase_of_mem ho]
    have hp := Finset.card_pos.mpr ⟨o, ho⟩
    simp only [Finset.mem_inter] at ho
    simp only [ho.1, ho.2, and_self, if_true]
    omega
  · rw [Finset.erase_eq_of_notMem ho]
    have hn : ¬(o ∈ A ∧ o ∈ nbrFinset x) := by simpa [Finset.mem_inter, and_comm] using ho
    simp [hn]

theorem lap_dirac_off (o x : Site2) (hx : x ≠ o) :
    lap (dirac o) x = if o ∈ nbrFinset x then 1 else 0 := by
  rw [lap, ← sum_neighbors]
  simp only [dirac_of_ne hx, mul_zero, sub_zero]
  simp [dirac, eq_comm]

theorem allowed_topple {V : Finset Site2} {h : Site2 → ℤ} {o : Site2}
    (ha : allowed V h) (hn : ∀ x ∈ V, 0 ≤ h x + lap (dirac o) x) :
    allowed V (fun x => h x + lap (dirac o) x) := by
  intro A hAV hf
  by_cases ho : o ∈ A
  · have hne : (A.erase o).Nonempty := by
      by_contra he
      have he' : A.erase o = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
      have hsub : A ⊆ {o} := by
        intro x hx
        by_cases hxo : x = o
        · simpa using hxo
        · have hm : x ∈ A.erase o := Finset.mem_erase.mpr ⟨hxo, hx⟩
          rw [he'] at hm
          simp at hm
      have hz : degree A o = 0 := by
        have hle := degree_mono hsub o
        have hz : degree {o} o = 0 := by
          simp [degree, Finset.inter_singleton_of_notMem (not_mem_neighbors_self o)]
        omega
      have hh := hf.2 o ho
      have hh0 := hn o (hAV ho)
      rw [hz] at hh
      dsimp only at hh
      omega
    apply ha (A.erase o) ((Finset.erase_subset o A).trans hAV)
    refine ⟨hne, ?_⟩
    intro x hx
    obtain ⟨hxo, hxA⟩ := Finset.mem_erase.mp hx
    have ht := hf.2 x hxA
    dsimp only at ht
    rw [degree_erase A o x, lap_dirac_off o x hxo] at ht
    simp only [ho, true_and] at ht
    omega
  · apply ha A hAV
    refine ⟨hf.1, ?_⟩
    intro x hx
    have ht := hf.2 x hx
    have hxo : x ≠ o := fun he => ho (he ▸ hx)
    have hl := lap_dirac_nonneg hxo
    linarith

theorem allowed_legal_list {V : Finset Site2} {h : Site2 → ℤ} {w : List Site2}
    (ha : allowed V h) (hw : LegalList h w) (hn : ∀ x, 0 ≤ h x) :
    allowed V (heightAfter h w) := by
  have hp : ∀ k, allowed V (fun x => h x + lap (prefixCounts w k) x) := by
    intro k
    induction k with
    | zero => simpa [prefix_zero, lap, nbrSumZ] using ha
    | succ k ih =>
      by_cases hk : k < w.length
      · have he : (fun x => h x + lap (prefixCounts w (k + 1)) x) =
            fun x => (h x + lap (prefixCounts w k) x) + lap (dirac w[k]) x := by
          funext x
          rw [prefix_succ_eq w k hk, lap_add]
          ring
        rw [he]
        apply allowed_topple ih
        intro x _
        rw [← congrFun he x]
        exact hw.heights_nonneg hn (k + 1) x
      · rw [prefix_eq_terminal w (k + 1) (by omega)]
        simpa only [prefix_eq_terminal w k (by omega)] using ih
  change allowed V (fun x => h x + lap (fun y => (listCounts w y : ℤ)) x)
  simpa only [prefix_eq_terminal w w.length le_rfl] using hp w.length

theorem allowed_congr {V : Finset Site2} {h g : Site2 → ℤ}
    (he : ∀ x ∈ V, h x = g x) : allowed V h ↔ allowed V g := by
  unfold allowed forbidden
  constructor <;> intro hh A hA hf <;> apply hh A hA
  · exact ⟨hf.1, fun x hx => by rw [he x (hA hx)]; exact hf.2 x hx⟩
  · exact ⟨hf.1, fun x hx => by rw [← he x (hA hx)]; exact hf.2 x hx⟩

/-- The literal union of all forbidden subsets of the finite active set. -/
def forbiddenCore (V : Finset Site2) (h : Site2 → ℤ) : Finset Site2 :=
  V.filter (fun x => ∃ A ⊆ V, forbidden h A ∧ x ∈ A)

theorem forbidden_subset_core {V A : Finset Site2} {h : Site2 → ℤ}
    (hA : A ⊆ V) (hf : forbidden h A) : A ⊆ forbiddenCore V h := by
  intro x hx
  exact Finset.mem_filter.mpr ⟨hA hx, A, hA, hf, hx⟩

theorem forbidden_core {V : Finset Site2} {h : Site2 → ℤ}
    (hne : ∃ A ⊆ V, forbidden h A) : forbidden h (forbiddenCore V h) := by
  obtain ⟨A, hA, hf⟩ := hne
  refine ⟨hf.1.mono (forbidden_subset_core hA hf), ?_⟩
  intro x hx
  obtain ⟨_, B, hB, hb, hxB⟩ := Finset.mem_filter.mp hx
  exact lt_of_lt_of_le (hb.2 x hxB) (by exact_mod_cast degree_mono (forbidden_subset_core hB hb) x)

theorem forbidden_core_subset (V : Finset Site2) (h : Site2 → ℤ) :
    forbiddenCore V h ⊆ V := Finset.filter_subset _ _

theorem degree_le_sdiff_add (H W : Finset Site2) (x : Site2) :
    degree H x ≤ degree (H \ W) x + degree W x := by
  have hs : nbrFinset x ∩ H ⊆ (nbrFinset x ∩ (H \ W)) ∪ (nbrFinset x ∩ W) := by
    intro y hy
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff] at hy ⊢
    by_cases hw : y ∈ W <;> tauto
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

theorem lap_counts_eq_degree {u : Counts} (hu : ∀ x, u x ≤ 1) (x : Site2) :
    lap (fun y => (u y : ℤ)) x = (degree u.support x : ℤ) -
      4 * if x ∈ u.support then 1 else 0 := by
  have he : (fun y => (u y : ℤ)) = fun y => if y ∈ u.support then 1 else 0 := by
    funext y
    by_cases hy : y ∈ u.support
    · have hn := Finsupp.mem_support_iff.mp hy
      have hh := hu y
      have h1 : u y = 1 := by omega
      simp [hy, h1]
    · simp [hy, Finsupp.notMem_support_iff.mp hy]
  rw [he, lap, ← degree_eq_sum]
  norm_num

end
end FiniteAvalanches.Sandpile.Waves
