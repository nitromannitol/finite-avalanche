module

public import FiniteAvalanches.Sandpile.Burning.Layers

@[expose] public section

/-! Every vertex of an allowed stable source field belongs to exactly one actual
burning layer. Uniqueness precedes the definition of its burning time. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (s : V)

theorem burn_remainder_antitone (h : SourceHeights G s) {n m : ℕ} (hnm : n ≤ m) :
    burnRemainder G s h m ⊆ burnRemainder G s h n := by
  induction m, hnm using Nat.le_induction with
  | base => exact fun _ hx => hx
  | succ m hm ih => exact (burn_remainder_succ_subset G s h m).trans ih

theorem burn_layer_disjoint (h : SourceHeights G s) {n m : ℕ} (hnm : n < m) :
    Disjoint (burnLayer G s h n) (burnLayer G s h m) := by
  apply Finset.disjoint_left.mpr
  intro v hvn hvm
  have hn := Finset.mem_sdiff.mp hvn
  have hm := Finset.mem_sdiff.mp hvm
  exact hn.2 (burn_remainder_antitone G s h hnm hm.1)

theorem exists_burn_layer_before (h : SourceHeights G s) (v : SourceVertex s) (n : ℕ)
    (hv : v ∉ burnRemainder G s h n) : ∃ m < n, v ∈ burnLayer G s h m := by
  induction n with
  | zero => exact False.elim (hv (Finset.mem_univ _))
  | succ n ih =>
    by_cases hn : v ∈ burnRemainder G s h n
    · exact ⟨n, Nat.lt_succ_self n, Finset.mem_sdiff.mpr ⟨hn, hv⟩⟩
    · obtain ⟨m, hm, hv⟩ := ih hn
      exact ⟨m, Nat.lt_succ_of_lt hm, hv⟩

theorem exists_unique_burn_layer (h : SourceHeights G s)
    (hn : noForbidden G (Finset.univ.erase s) h) (v : SourceVertex s) :
    ∃! n, v ∈ burnLayer G s h n := by
  have he := burn_remainder_empty G s h hn
  obtain ⟨n, _, hv⟩ := exists_burn_layer_before G s h v (Fintype.card (SourceVertex s))
    (by rw [he]; simp)
  refine ⟨n, hv, ?_⟩
  intro m hm
  rcases lt_trichotomy m n with hmn | hmn | hmn
  · exact False.elim (Finset.disjoint_left.mp (burn_layer_disjoint G s h hmn) hm hv)
  · exact hmn
  · exact False.elim (Finset.disjoint_left.mp (burn_layer_disjoint G s h hmn) hv hm)

/-- The unique actual layer index, defined only after its full existence/uniqueness proof. -/
def burnTime (h : SourceHeights G s) (hn : noForbidden G (Finset.univ.erase s) h)
    (v : SourceVertex s) : ℕ := (exists_unique_burn_layer G s h hn v).choose

theorem burn_time_spec (h : SourceHeights G s) (hn : noForbidden G (Finset.univ.erase s) h)
    (v : SourceVertex s) : v ∈ burnLayer G s h (burnTime G s h hn v) :=
  (exists_unique_burn_layer G s h hn v).choose_spec.1

theorem burn_time_eq_iff (h : SourceHeights G s) (hn : noForbidden G (Finset.univ.erase s) h)
    (v : SourceVertex s) (n : ℕ) : burnTime G s h hn v = n ↔ v ∈ burnLayer G s h n := by
  constructor
  · intro he
    exact he ▸ burn_time_spec G s h hn v
  · intro hv
    exact ((exists_unique_burn_layer G s h hn v).choose_spec.2 n hv).symm

theorem burn_time_lt_card (h : SourceHeights G s) (hn : noForbidden G (Finset.univ.erase s) h)
    (v : SourceVertex s) : burnTime G s h hn v < Fintype.card (SourceVertex s) := by
  obtain ⟨n, hlt, hv⟩ := exists_burn_layer_before G s h v (Fintype.card (SourceVertex s))
    (by rw [burn_remainder_empty G s h hn]; simp)
  rw [(burn_time_eq_iff G s h hn v n).mpr hv]
  exact hlt

end
end FiniteAvalanches.Sandpile.Burning
