module

public import FiniteAvalanches.Sandpile.Burning.InducedGraph

@[expose] public section

/-! Stable heights occupy every active vertex with its original copied degree.
A burn removes one eligible unheld vertex. Termination and uniqueness precede
choice of the stopping set; no recurrence or spanning-tree law is assumed. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (U : Finset V)

abbrev Heights := (v : InducedVertex U) → Fin (degree G v.val)

def activeDegree (A : Finset (InducedVertex U)) (x : InducedVertex U) : ℕ :=
  degreeInto G (A.image Subtype.val) x.val

theorem active_degree_mono {A C : Finset (InducedVertex U)} (h : A ⊆ C)
    (x : InducedVertex U) : activeDegree G U A x ≤ activeDegree G U C x :=
  degree_into_mono G (Finset.image_subset_image h) x.val

/-- The no-forbidden-subconfiguration predicate, distinct from Markov recurrence. -/
def noForbidden (h : Heights G U) : Prop :=
  ∀ A : Finset (InducedVertex U),
    ¬(A.Nonempty ∧ ∀ x ∈ A, (h x).val < activeDegree G U A x)

/-- A closed stopping candidate exempts exactly the held vertices. -/
def heldClosed (h : Heights G U) (B A : Finset (InducedVertex U)) : Prop :=
  B ⊆ A ∧ ∀ x ∈ A, x ∉ B → (h x).val < activeDegree G U A x

inductive BurnTrace (h : Heights G U) (B : Finset (InducedVertex U)) :
    Finset (InducedVertex U) → List (InducedVertex U) → Finset (InducedVertex U) → Prop
  | nil {A} (ht : ∀ x ∈ A, x ∉ B → (h x).val < activeDegree G U A x) :
      BurnTrace h B A [] A
  | cons {A w C x} (hx : x ∈ A) (hb : x ∉ B)
      (ht : activeDegree G U A x ≤ (h x).val)
      (tail : BurnTrace h B (A.erase x) w C) : BurnTrace h B A (x :: w) C

theorem exists_burn_trace (h : Heights G U) (B A : Finset (InducedVertex U)) :
    ∃ w C, BurnTrace G U h B A w C := by
  exact go A
where
  go (A : Finset (InducedVertex U)) : ∃ w C, BurnTrace G U h B A w C := by
    by_cases ht : ∀ x ∈ A, x ∉ B → (h x).val < activeDegree G U A x
    · exact ⟨[], A, .nil ht⟩
    · push Not at ht
      obtain ⟨x, hx, hb, ht⟩ := ht
      obtain ⟨w, C, hw⟩ := go (A.erase x)
      exact ⟨x :: w, C, .cons hx hb ht hw⟩
  termination_by A.card
  decreasing_by exact Finset.card_erase_lt_of_mem hx

theorem BurnTrace.final_subset {h : Heights G U} {B A C : Finset (InducedVertex U)}
    {w : List (InducedVertex U)} (hw : BurnTrace G U h B A w C) : C ⊆ A := by
  induction hw with
  | nil => exact fun _ hx => hx
  | cons _ _ _ _ ih => exact ih.trans (Finset.erase_subset _ _)

theorem BurnTrace.final_closed {h : Heights G U} {B A C : Finset (InducedVertex U)}
    {w : List (InducedVertex U)} (hw : BurnTrace G U h B A w C) (hB : B ⊆ A) :
    heldClosed G U h B C := by
  induction hw with
  | nil ht => exact ⟨hB, ht⟩
  | @cons A w C x hx hb ht tail ih =>
    apply ih
    intro y hy
    exact Finset.mem_erase.mpr ⟨fun he => hb (he ▸ hy), hB hy⟩

theorem BurnTrace.closed_subset_final {h : Heights G U}
    {B A C D : Finset (InducedVertex U)} {w : List (InducedVertex U)}
    (hw : BurnTrace G U h B A w C) (hD : D ⊆ A) (hd : heldClosed G U h B D) : D ⊆ C := by
  induction hw with
  | nil => exact hD
  | @cons A w C x hx hb ht tail ih =>
    apply ih
    intro y hy
    refine Finset.mem_erase.mpr ⟨?_, hD hy⟩
    intro he
    subst y
    have hh := hd.2 x hy hb
    have hm := active_degree_mono G U hD x
    omega

theorem BurnTrace.final_unique {h : Heights G U} {B A C D : Finset (InducedVertex U)}
    {w v : List (InducedVertex U)} (hw : BurnTrace G U h B A w C)
    (hv : BurnTrace G U h B A v D) (hB : B ⊆ A) : C = D := by
  apply Finset.Subset.antisymm
  · exact BurnTrace.closed_subset_final G U hv (BurnTrace.final_subset G U hw) (BurnTrace.final_closed G U hw hB)
  · exact BurnTrace.closed_subset_final G U hw (BurnTrace.final_subset G U hv) (BurnTrace.final_closed G U hv hB)

theorem exists_unique_burn_final (h : Heights G U) (B : Finset (InducedVertex U)) :
    ∃! C, ∃ w, BurnTrace G U h B Finset.univ w C := by
  obtain ⟨w, C, hw⟩ := exists_burn_trace G U h B Finset.univ
  exact ⟨C, ⟨w, hw⟩, fun D ⟨v, hv⟩ => BurnTrace.final_unique G U hv hw (Finset.subset_univ _)⟩

/-- The unique actual terminal set, chosen after finite operational existence and uniqueness. -/
def heldBurning (h : Heights G U) (B : Finset (InducedVertex U)) :
    Finset (InducedVertex U) := (exists_unique_burn_final G U h B).choose

theorem held_burning_realizes (h : Heights G U) (B : Finset (InducedVertex U)) :
    ∃ w, BurnTrace G U h B Finset.univ w (heldBurning G U h B) :=
  (exists_unique_burn_final G U h B).choose_spec.1

theorem held_burning_largest (h : Heights G U) (B : Finset (InducedVertex U)) :
    heldClosed G U h B (heldBurning G U h B) ∧
      ∀ D, heldClosed G U h B D → D ⊆ heldBurning G U h B := by
  obtain ⟨w, hw⟩ := held_burning_realizes G U h B
  exact ⟨BurnTrace.final_closed G U hw (Finset.subset_univ _),
    fun D hd => BurnTrace.closed_subset_final G U hw (Finset.subset_univ _) hd⟩

theorem held_burning_eq_iff (h : Heights G U) (B A : Finset (InducedVertex U)) :
    heldBurning G U h B = A ↔
      heldClosed G U h B A ∧ ∀ D, heldClosed G U h B D → D ⊆ A := by
  constructor
  · intro he
    rw [← he]
    exact held_burning_largest G U h B
  · rintro ⟨ha, hmax⟩
    obtain ⟨hc, hsub⟩ := held_burning_largest G U h B
    exact Finset.Subset.antisymm (hmax _ hc) (hsub _ ha)

theorem held_burning_empty_of_noForbidden (h : Heights G U) (hn : noForbidden G U h) :
    heldBurning G U h ∅ = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro x hx
  have hc := (held_burning_largest G U h ∅).1
  exact hn _ ⟨⟨x, hx⟩, fun y hy => hc.2 y hy (by simp)⟩

end
end FiniteAvalanches.Sandpile.Burning
