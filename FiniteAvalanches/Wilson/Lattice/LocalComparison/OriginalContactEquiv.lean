import FiniteAvalanches.Wilson.Lattice.LocalComparison.MarkedBoundary

set_option autoImplicit false
namespace LocalBoxContraction
open LatticeProb FiniteAvalanches FiniteAvalanches.Wilson FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Electrical FiniteAvalanches.Electrical.Plane.SourceLattice
open scoped Classical BigOperators
noncomputable section

abbrev RawColoredDart (D : Finset (Site 2)) (σ : ColorField) :=
  {z : ↥(domainCopies D) × Bool //
    Plane.tail originalA originalB (z.1.val,z.2) ∉ D ∧
      σ (Plane.head originalA originalB (z.1.val,z.2)) = true}

abbrev ColoredExteriorDirection (D : Finset (Site 2)) (σ : ColorField) :=
  {xd : ↥(exteriorSites D) × FiniteWired.Direction //
    σ (xd.1.val + FiniteWired.step xd.2) = true}

theorem color_true_inside (D : Finset (Site 2)) (σ : ColorField)
    (hσ : ∀ x ∉ D, σ x = false) {x : Site 2} (hx : σ x = true) : x ∈ D := by
  by_contra hn
  have he := (hσ x hn).symm.trans hx
  cases he

theorem original_tail_neighbor_head (z : Plane.Dart OriginalCopy) :
    Plane.tail originalA originalB z ∈ nbrFinset (Plane.head originalA originalB z) := by
  apply (FiniteWired.mem_neighbors_iff _ _).mpr
  rcases z with ⟨⟨x,i⟩,b⟩
  cases b
  · exact ⟨i,Or.inr rfl⟩
  · exact ⟨i,Or.inl rfl⟩

theorem colored_tail_exterior (D : Finset (Site 2)) (σ : ColorField)
    (hσ : ∀ x ∉ D, σ x = false) (z : RawColoredDart D σ) :
    Plane.tail originalA originalB (z.val.1.val,z.val.2) ∈ exteriorSites D := by
  refine Finset.mem_filter.mpr ⟨?_,z.property.1⟩
  exact Finset.mem_biUnion.mpr ⟨_, color_true_inside D σ hσ z.property.2,
    original_tail_neighbor_head _⟩

theorem incidentID_domain_of_colored (D : Finset (Site 2)) (σ : ColorField)
    (hσ : ∀ x ∉ D, σ x = false) (xd : ColoredExteriorDirection D σ) :
    incidentID xd.val.1.val xd.val.2 ∈ domainCopies D := by
  have hd := color_true_inside D σ hσ xd.property
  apply (mem_domainCopies D _).mpr
  rcases hdir : xd.val.2 with ⟨i,b⟩
  rw [hdir] at hd
  cases b
  · left
    simpa only [incidentID, Bool.false_eq_true, if_false, originalA,
      FiniteWired.step, ← sub_eq_add_neg] using hd
  · right
    simpa only [incidentID, if_true, originalB, FiniteWired.step] using hd

/-- Each boundary neighbor occurrence is its own original dart, retaining parallel copies. -/
def boundaryDirectionEquiv (D : Finset (Site 2)) (σ : ColorField)
    (hσ : ∀ x ∉ D, σ x = false) : RawColoredDart D σ ≃ ColoredExteriorDirection D σ where
  toFun z := ⟨(⟨Plane.tail originalA originalB (z.val.1.val,z.val.2), colored_tail_exterior D σ hσ z⟩,
    (z.val.1.val.2,!z.val.2)), by
      have he := congrArg (Plane.head originalA originalB) (originalDart_reconstruct (z.val.1.val,z.val.2))
      rw [originalDart_head] at he
      rw [he]
      exact z.property.2⟩
  invFun xd := ⟨(⟨incidentID xd.val.1.val xd.val.2, incidentID_domain_of_colored D σ hσ xd⟩,
    !xd.val.2.2), by
      change Plane.tail originalA originalB (originalDart xd.val.1.val xd.val.2) ∉ D ∧
        σ (Plane.head originalA originalB (originalDart xd.val.1.val xd.val.2)) = true
      rw [originalDart_tail, originalDart_head]
      exact ⟨(Finset.mem_filter.mp xd.val.1.property).2,xd.property⟩⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (originalDart_reconstruct (z.val.1.val,z.val.2))
    · exact Bool.not_not _
  right_inv xd := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact originalDart_tail _ _
    · apply Prod.ext
      · rfl
      · exact Bool.not_not _

def rawBoundaryCount (D : Finset (Site 2)) (σ : ColorField) : ℕ :=
  ∑ e ∈ domainCopies D, ∑ b : Bool,
    if Plane.tail originalA originalB (e,b) ∉ D ∧
      σ (Plane.head originalA originalB (e,b)) = true then 1 else 0

theorem rawBoundaryCount_card (D : Finset (Site 2)) (σ : ColorField) :
    rawBoundaryCount D σ = Nat.card (RawColoredDart D σ) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type,
    Finset.univ_eq_attach]
  exact (Finset.sum_attach _ _).symm

theorem neighbors_direction_image (x : Site 2) :
    (Finset.univ : Finset FiniteWired.Direction).image (fun d => x + FiniteWired.step d) = nbrFinset x := by
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and, nbrFinset,
    Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨i,b⟩,rfl⟩
    cases b
    · exact ⟨i,Or.inr (by simp [FiniteWired.step,sub_eq_add_neg])⟩
    · exact ⟨i,Or.inl rfl⟩
  · rintro ⟨i,hi | hi⟩
    · exact ⟨(i,true),hi.symm⟩
    · exact ⟨(i,false),by simpa only [FiniteWired.step, Bool.false_eq_true, if_false,
        ← sub_eq_add_neg] using hi.symm⟩

theorem contacts_direction_sum (K : Finset (Site 2)) (σ : ColorField) :
    contacts K σ = ∑ x ∈ K, ∑ d : FiniteWired.Direction, if σ (x + FiniteWired.step d) then 1 else 0 := by
  apply Finset.sum_congr rfl
  intro x _
  rw [← neighbors_direction_image x, Finset.sum_image]
  intro d _ e _ h
  exact FiniteWired.step_injective (add_left_cancel h)

theorem coloredExteriorDirection_card (D : Finset (Site 2)) (σ : ColorField) :
    Nat.card (ColoredExteriorDirection D σ) = contacts (exteriorSites D) σ := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type,
    Finset.univ_eq_attach, contacts_direction_sum]
  exact Finset.sum_attach (exteriorSites D) (fun x =>
    ∑ d : FiniteWired.Direction, if σ (x + FiniteWired.step d) = true then (1 : ℕ) else 0)

/-- The whole original-copy boundary count equals the literal exterior neighbor-contact sum. -/
theorem rawBoundaryCount_contacts (D : Finset (Site 2)) (σ : ColorField)
    (hσ : ∀ x ∉ D, σ x = false) : rawBoundaryCount D σ = contacts (exteriorSites D) σ := by
  rw [rawBoundaryCount_card, Nat.card_congr (boundaryDirectionEquiv D σ hσ),
    coloredExteriorDirection_card]

/-- Every exterior contact contribution outside this exact finite support is zero. -/
theorem exterior_off_support_zero (D : Finset (Site 2)) (σ : ColorField)
    (hσ : ∀ x ∉ D, σ x = false) (x : Site 2) (hx : x ∉ D)
    (hs : x ∉ exteriorSites D) :
    (∑ y ∈ nbrFinset x, if σ y then (1 : ℕ) else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro y hy
  have hn : σ y ≠ true := by
    intro hc
    have hd := color_true_inside D σ hσ hc
    have hxy := (FiniteWired.mem_neighbors_iff x y).mp hy
    have hyx := (FiniteWired.mem_neighbors_iff y x).mpr ((lattice 2).symm.symm x y hxy)
    exact hs (Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨y,hd,hyx⟩,hx⟩)
  exact if_neg hn

/-- Any finite source window containing the full contributing support computes the same L(A). -/
theorem exteriorContacts_eq_window (D : Finset (Site 2)) (σ : ColorField)
    (hσ : ∀ x ∉ D, σ x = false) (A : Set (Site 2)) (hA : A ⊆ (D : Set (Site 2))ᶜ)
    (K : Finset (Site 2)) (hKA : (K : Set (Site 2)) ⊆ A)
    (hcover : ∀ x ∈ exteriorSites D, x ∈ A → x ∈ K) :
    exteriorContacts D A σ = contacts K σ := by
  unfold exteriorContacts contacts
  apply Finset.sum_subset
  · intro x hx
    obtain ⟨hs,ha⟩ := Finset.mem_filter.mp hx
    exact hcover x hs ha
  · intro x hx hn
    have ha := hKA hx
    have hs : x ∉ exteriorSites D := fun hs => hn (Finset.mem_filter.mpr ⟨hs,ha⟩)
    exact exterior_off_support_zero D σ hσ x (hA ha) hs

end
end LocalBoxContraction
