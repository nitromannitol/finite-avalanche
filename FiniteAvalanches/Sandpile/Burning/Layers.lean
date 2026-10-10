module

public import FiniteAvalanches.Sandpile.Burning.Restriction
public import FiniteAvalanches.Sandpile.Burning.SourceFields

@[expose] public section

/-! Deterministic burning layers remove every presently eligible nonsink
vertex. This is the finite burning test, not parallel sandpile stabilization. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (s : V)

def burnRemainder (h : SourceHeights G s) : ℕ → Finset (SourceVertex s)
  | 0 => Finset.univ
  | n + 1 => (burnRemainder h n).filter fun v =>
      (h v).val < activeDegree G (Finset.univ.erase s) (burnRemainder h n) v

def burnLayer (h : SourceHeights G s) (n : ℕ) : Finset (SourceVertex s) :=
  burnRemainder G s h n \ burnRemainder G s h (n + 1)

def previousBurnt (h : SourceHeights G s) : ℕ → Finset V
  | 0 => {s}
  | n + 1 => (burnLayer G s h n).image Subtype.val

theorem burn_remainder_succ_subset (h : SourceHeights G s) (n : ℕ) :
    burnRemainder G s h (n + 1) ⊆ burnRemainder G s h n := Finset.filter_subset _ _

theorem mem_burn_layer (h : SourceHeights G s) (n : ℕ) (v : SourceVertex s) :
    v ∈ burnLayer G s h n ↔ v ∈ burnRemainder G s h n ∧
      activeDegree G (Finset.univ.erase s) (burnRemainder G s h n) v ≤ (h v).val := by
  simp only [burnLayer, Finset.mem_sdiff, burnRemainder, Finset.mem_filter]
  constructor
  · rintro ⟨hv, hh⟩
    refine ⟨hv, ?_⟩
    by_contra ht
    exact hh ⟨hv, by omega⟩
  · rintro ⟨hv, ht⟩
    exact ⟨hv, fun hf => Nat.not_lt_of_ge ht hf.2⟩

theorem burn_remainder_card_lt (h : SourceHeights G s)
    (hn : noForbidden G (Finset.univ.erase s) h) (n : ℕ)
    (hne : (burnRemainder G s h n).Nonempty) :
    (burnRemainder G s h (n + 1)).card < (burnRemainder G s h n).card := by
  have hex : ∃ v ∈ burnRemainder G s h n,
      activeDegree G (Finset.univ.erase s) (burnRemainder G s h n) v ≤ (h v).val := by
    by_contra he
    push Not at he
    exact hn _ ⟨hne, he⟩
  obtain ⟨v, hv, ht⟩ := hex
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨burn_remainder_succ_subset G s h n, ?_⟩
  intro he
  have hv' : v ∈ burnRemainder G s h (n + 1) := he.symm ▸ hv
  have hh := (Finset.mem_filter.mp hv').2
  omega

theorem burn_remainder_card_le (h : SourceHeights G s)
    (hn : noForbidden G (Finset.univ.erase s) h) (n : ℕ) :
    (burnRemainder G s h n).card ≤ Fintype.card (SourceVertex s) - n := by
  induction n with
  | zero => simp [burnRemainder]
  | succ n ih =>
    by_cases he : burnRemainder G s h n = ∅
    · have hem : burnRemainder G s h (n + 1) = ∅ :=
        Finset.Subset.antisymm (by simpa only [he] using burn_remainder_succ_subset G s h n)
          (Finset.empty_subset _)
      simp [hem]
    · have hc := burn_remainder_card_lt G s h hn n (Finset.nonempty_iff_ne_empty.mpr he)
      have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
      omega

theorem burn_remainder_empty (h : SourceHeights G s)
    (hn : noForbidden G (Finset.univ.erase s) h) :
    burnRemainder G s h (Fintype.card (SourceVertex s)) = ∅ := by
  apply Finset.card_eq_zero.mp
  have hc := burn_remainder_card_le G s h hn (Fintype.card (SourceVertex s))
  omega

theorem source_vertices_image :
    (Finset.univ : Finset (SourceVertex s)).image Subtype.val = Finset.univ.erase s := by
  ext v
  constructor
  · intro hv
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
    exact x.property
  · intro hv
    exact Finset.mem_image.mpr ⟨⟨v, hv⟩, Finset.mem_univ _, rfl⟩

theorem first_layer_degree (v : SourceVertex s) :
    activeDegree G (Finset.univ.erase s) Finset.univ v + degreeInto G {s} v.val = degree G v.val := by
  unfold activeDegree
  rw [source_vertices_image]
  simpa only [Finset.sdiff_singleton_eq_erase] using degree_into_compl G {s} v.val

theorem later_layer_degree (h : SourceHeights G s) (n : ℕ) (v : SourceVertex s) :
    activeDegree G (Finset.univ.erase s) (burnRemainder G s h (n + 1)) v +
      degreeInto G (previousBurnt G s h (n + 1)) v.val =
        activeDegree G (Finset.univ.erase s) (burnRemainder G s h n) v := by
  have hd := active_degree_union G (Finset.univ.erase s)
    (Finset.sdiff_disjoint : Disjoint (burnRemainder G s h n \ burnRemainder G s h (n + 1))
      (burnRemainder G s h (n + 1))) v
  rw [Finset.sdiff_union_of_subset (burn_remainder_succ_subset G s h n)] at hd
  change _ + activeDegree G (Finset.univ.erase s) (burnLayer G s h n) v = _
  change activeDegree G (Finset.univ.erase s) (burnRemainder G s h n) v =
    activeDegree G (Finset.univ.erase s) (burnLayer G s h n) v +
      activeDegree G (Finset.univ.erase s) (burnRemainder G s h (n + 1)) v at hd
  omega

end
end FiniteAvalanches.Sandpile.Burning
