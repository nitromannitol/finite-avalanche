import FiniteAvalanches.Sandpile.Components.Graphs
import FiniteAvalanches.Sandpile.Waves.FiniteDetermination
import FiniteAvalanches.Sandpile.TreeLaw

/-! Concrete source components exercise empty domains, degree zero and sink copies. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves
open scoped Classical
noncomputable section

/-- The singleton source shape is admitted at every radius. -/
def singletonShape {N : ℕ} (o : FiniteWired.Active N) : ComponentShape o :=
  ⟨{FiniteWired.site o}, by
    intro x hx
    simpa only [Finset.mem_singleton.mp hx] using site_mem_box o,
    Finset.mem_singleton_self _⟩

/-- The whole box is admitted; its complementary induced graph is the singleton sink. -/
def fullShape {N : ℕ} (o : FiniteWired.Active N) : ComponentShape o :=
  ⟨boxSites N, Finset.Subset.refl _, site_mem_box o⟩

theorem singleton_inner_unique {N : ℕ} (o : FiniteWired.Active N) :
    ∃! _r : InnerAllowed o (singletonShape o), True := by
  let f : InnerField o (singletonShape o) := fun x => by
    have h : False := by simpa [singletonShape] using x.property
    exact h.elim
  have hf : allowedOn ((singletonShape o).val.erase (FiniteWired.site o))
      (fun x => (f x).val) := by
    intro A hA hforb
    have he : A = ∅ := Finset.subset_empty.mp (by simpa [singletonShape] using hA)
    simpa [he] using hforb.1
  refine ⟨⟨f, hf⟩, trivial, ?_⟩
  intro g _
  apply Subtype.ext
  funext x
  have h : False := by simpa [singletonShape] using x.property
  exact h.elim

theorem full_outer_unique {N : ℕ} (o : FiniteWired.Active N) :
    ∃! _r : OuterAllowed (fullShape o), True := by
  let f : OuterField (fullShape o) := fun x => by
    have h : False := by simpa [fullShape] using x.property
    exact h.elim
  have hf : allowedOn (boxSites N \ (fullShape o).val) (fun x => (f x).val) := by
    intro A hA hforb
    have he : A = ∅ := Finset.subset_empty.mp (by simpa [fullShape] using hA)
    simpa [he] using hforb.1
  refine ⟨⟨f, hf⟩, trivial, ?_⟩
  intro g _
  apply Subtype.ext
  funext x
  have h : False := by simpa [fullShape] using x.property
  exact h.elim

/-- A degree-zero vertex is retained in the dependent product, making stable fields empty. -/
theorem inner_field_empty_of_zero_degree {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (x : {x : Site2 // x ∈ C.val.erase (FiniteWired.site o)})
    (hx : degree C.val x.val = 0) : IsEmpty (InnerField o C) := by
  constructor
  intro r
  have h := (r x).isLt
  omega

theorem outer_field_empty_of_degree_four {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (x : {x : Site2 // x ∈ boxSites N \ C.val})
    (hx : degree C.val x.val = 4) : IsEmpty (OuterField C) := by
  constructor
  intro r
  have h := (r x).isLt
  omega

/-- Disconnected closed source-free parts have no allowed field, without a connectivity binder. -/
theorem inner_allowed_empty_of_closed_part {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (A : Finset Site2) (hne : A.Nonempty)
    (hsub : A ⊆ C.val.erase (FiniteWired.site o))
    (hdeg : ∀ x ∈ A, degree C.val x = degree A x) : IsEmpty (InnerAllowed o C) := by
  constructor
  intro r
  apply r.property A hsub
  refine ⟨hne, ?_⟩
  intro x hx
  exact (r.val ⟨x, hsub hx⟩).isLt.trans_le (hdeg x hx).le

/-- Every raw core fibre inhabitant proves its shape admissible. -/
theorem core_field_shape {N : ℕ} {o : FiniteWired.Active N} {C : Finset Site2}
    (h : CoreField o C) : C ⊆ boxSites N ∧ FiniteWired.site o ∈ C := by
  rw [← h.property]
  exact ⟨forbidden_core_subset _ _, source_mem_core h.val.val⟩

theorem no_empty_shape {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    C.val ≠ ∅ := by
  intro he
  have hh := C.property.2
  rw [he] at hh
  exact Finset.notMem_empty _ hh

/-- Counts refer to actual allowed-field carriers; no burning or tree-count equality is assumed. -/
theorem card_core_field {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    Nat.card (CoreField o C.val) = Nat.card (InnerAllowed o C) * Nat.card (OuterAllowed C) := by
  rw [Nat.card_congr (componentFieldEquiv (C := C)), Nat.card_prod]

/-- The full off-source field is uniquely characterized by both reconstruction formulas. -/
theorem join_field_unique {N : ℕ} {o : FiniteWired.Active N} {C : ComponentShape o}
    (rC : InnerField o C) (rD : OuterField C) (h : OffField N o)
    (hi : ∀ x : {x : Site2 // x ∈ C.val.erase (FiniteWired.site o)},
      wiredHeight (-1) h x.val = ((rC x).val : ℤ))
    (ho : ∀ x : {x : Site2 // x ∈ boxSites N \ C.val},
      wiredHeight (-1) h x.val = ((rD x).val : ℤ) + (degree C.val x.val : ℤ)) :
    h = joinField rC rD := by
  funext x
  apply Fin.ext
  have hxo : FiniteWired.site x.val ≠ FiniteWired.site o :=
    fun he => x.property (FiniteWired.site_injective N he)
  by_cases hx : FiniteWired.site x.val ∈ C.val
  · let y : {x : Site2 // x ∈ C.val.erase (FiniteWired.site o)} :=
      ⟨FiniteWired.site x.val, Finset.mem_erase.mpr ⟨hxo, hx⟩⟩
    have he := (hi y).trans (join_field_height_inner rC rD y).symm
    rw [wired_height_off_vertex, wired_height_off_vertex] at he
    exact_mod_cast he
  · let y : {x : Site2 // x ∈ boxSites N \ C.val} :=
      ⟨FiniteWired.site x.val, Finset.mem_sdiff.mpr ⟨site_mem_box x.val, hx⟩⟩
    have he := (ho y).trans (join_field_height_outer rC rD y).symm
    rw [wired_height_off_vertex, wired_height_off_vertex] at he
    exact_mod_cast he

end
end FiniteAvalanches.Sandpile.Components
