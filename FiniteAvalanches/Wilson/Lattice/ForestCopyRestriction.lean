import FiniteAvalanches.Wilson.Lattice.NonrootVertices

set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.WiredBoxCopies
open LatticeProb FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

 theorem copyInLarger_direction {N M : ℕ} (hNM : N ≤ M)
    (x : FiniteWired.Active N) (d : FiniteWired.Direction) :
    copyInLarger hNM (FiniteWired.directionEdge x d) =
      FiniteWired.directionEdge (activeEmbedding hNM x) d := by
  apply originalCopyEdge_injective M
  rw [copyInLarger_original]
  apply Subtype.ext
  rw [originalCopyEdge_direction,originalCopyEdge_direction,site_activeEmbedding]

 theorem copyInLarger_covers_incident {N M : ℕ} (hNM : N ≤ M)
    (x : FiniteWired.Active N) (e : FiniteWired.Edge M)
    (he : FiniteAvalanches.Sandpile.Components.incident (activeEmbedding hNM x) e) :
    ∃ f : FiniteWired.Edge N, copyInLarger hNM f = e := by
  obtain ⟨d,hd⟩ := FiniteAvalanches.Sandpile.Components.exists_direction_of_incident _ e he
  exact ⟨FiniteWired.directionEdge x d,(copyInLarger_direction hNM x d).trans hd⟩

private theorem outside_of_no_small_vertex {N M : ℕ} (hNM : N ≤ M)
    (v : FiniteWired.Vertex M)
    (hv : ¬∃ x : FiniteWired.Active N, v = some (activeEmbedding hNM x)) :
    v = none ∨ ∃ x, v = some x ∧ ¬FiniteWired.inBox N (FiniteWired.site x) := by
  cases v with
  | none => exact Or.inl rfl
  | some x =>
    refine Or.inr ⟨x,rfl,?_⟩
    intro hx
    let a := FiniteWired.activeOfSite N (FiniteWired.site x) hx
    have ha : activeEmbedding hNM a = x := FiniteWired.site_injective M rfl
    exact hv ⟨a,congrArg some ha.symm⟩

/-- Every selected large-box copy is the image of exactly one original
small-box copy. Root-root exterior copies cannot create a hidden fiber factor. -/
theorem selected_copy_in_range {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one)
    (F : FiniteForest R M) (e : FiniteWired.Edge M) (he : e ∈ F.val) :
    ∃ f : FiniteWired.Edge N, copyInLarger hNM f = e := by
  by_cases hl : ∃ x : FiniteWired.Active N,
      (FiniteWired.endpoints e).1 = some (activeEmbedding hNM x)
  · obtain ⟨x,hx⟩ := hl
    exact copyInLarger_covers_incident hNM x e (Or.inl hx)
  · by_cases hr : ∃ x : FiniteWired.Active N,
        (FiniteWired.endpoints e).2 = some (activeEmbedding hNM x)
    · obtain ⟨x,hx⟩ := hr
      exact copyInLarger_covers_incident hNM x e (Or.inr hx)
    · exact (exterior_root_copies_absent R houtside F e
        (outside_of_no_small_vertex hNM _ hl)
        (outside_of_no_small_vertex hNM _ hr) he).elim

/-- Literal inverse copied subset, not a color configuration or endpoint set. -/
def restrictCopies {N M : ℕ} (hNM : N ≤ M) (F : Finset (FiniteWired.Edge M)) :
    Finset (FiniteWired.Edge N) := Finset.univ.filter (fun e => copyInLarger hNM e ∈ F)

@[simp] theorem mem_restrictCopies {N M : ℕ} (hNM : N ≤ M)
    (F : Finset (FiniteWired.Edge M)) (e : FiniteWired.Edge N) :
    e ∈ restrictCopies hNM F ↔ copyInLarger hNM e ∈ F := by
  simp only [restrictCopies,Finset.mem_filter,Finset.mem_univ,true_and]

 theorem restrictCopies_image {N M : ℕ} (hNM : N ≤ M)
    (F : Finset (FiniteWired.Edge N)) :
    restrictCopies hNM (F.image (copyInLarger hNM)) = F := by
  ext e
  simp only [mem_restrictCopies,Finset.mem_image]
  constructor
  · rintro ⟨f,hf,hfe⟩
    exact (copyInLarger_injective hNM hfe) ▸ hf
  · intro he
    exact ⟨e,he,rfl⟩

 theorem image_restrictCopies_forest {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one)
    (F : FiniteForest R M) :
    (restrictCopies hNM F.val).image (copyInLarger hNM) = F.val := by
  ext e
  constructor
  · intro he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    exact (mem_restrictCopies hNM F.val f).mp hf
  · intro he
    obtain ⟨f,hf⟩ := selected_copy_in_range hNM R houtside F e he
    exact Finset.mem_image.mpr ⟨f,(mem_restrictCopies hNM F.val f).mpr (hf.symm ▸ he),hf⟩

end
end FiniteAvalanches.Wilson.Lattice.WiredBoxCopies
