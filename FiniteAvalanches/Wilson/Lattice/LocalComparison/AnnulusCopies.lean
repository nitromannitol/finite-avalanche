import FiniteAvalanches.Wilson.Lattice.LocalComparison.FullContacts
import FiniteAvalanches.RevealedRoots.FiniteContactLoss

set_option autoImplicit false
namespace LocalAnnulusCopies
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteWired FiniteAvalanches.Needle FiniteAvalanches.RevealedRoots
open FiniteAvalanches.Electrical
open scoped Classical BigOperators
noncomputable section

/-- All possible exterior endpoints of original box boundary copies. -/
def outerSites (N : ℕ) : Finset (Site 2) := (boxSites (N+1)).filter (fun x => x ∉ boxSites N)

/-- The four original lattice directions, with their orientation reversed. -/
def reverse (d : Direction) : Direction := (d.1,!d.2)

theorem reverse_reverse (d : Direction) : reverse (reverse d) = d := by
  rcases d with ⟨i,b⟩
  cases b <;> rfl

theorem step_reverse (d : Direction) : step (reverse d) = -step d := by
  rcases d with ⟨i,b⟩
  cases b
  · simp only [reverse,step,Bool.not_false,Bool.false_eq_true,if_false,if_true,neg_neg]
  · rfl

/-- An exterior-origin incidence with an active neighbor, retaining its direction. -/
abbrev ExteriorIncidence (N : ℕ) :=
  {p : ↥(outerSites N) × Direction // inBox N (p.1.val+step p.2)}

/-- The same original copy in the wired exit carrier. -/
def toExit (N : ℕ) (p : ExteriorIncidence N) : ExitEdge N :=
  ⟨(activeOfSite N (p.val.1.val+step p.val.2) p.property,reverse p.val.2),by
    rw [site_activeOfSite,step_reverse,add_neg_cancel_right]
    exact fun h => (Finset.mem_filter.mp p.val.1.property).2 ((mem_box_sites N _).mpr h)⟩

/-- An actual wired exit has an exterior endpoint in the one-layer shell. -/
def fromExit (N : ℕ) (e : ExitEdge N) : ExteriorIncidence N := by
  let x := site e.val.1+step e.val.2
  have hxB : x ∈ boxSites (N+1) := by
    apply LocalFullContacts.neighbor_box N x (site e.val.1)
      ((mem_box_sites N _).mpr (fun i => (e.val.1 i).property))
    apply (mem_neighbors_iff x (site e.val.1)).mpr
    have ha : x ∈ nbrFinset (site e.val.1) := by
      rw [neighbors_eq_directions]
      exact Finset.mem_image.mpr ⟨e.val.2,Finset.mem_univ _,rfl⟩
    exact ((mem_neighbors_iff _ _).mp ha).symm
  have hxO : x ∉ boxSites N := fun h => e.property ((mem_box_sites N _).mp h)
  refine ⟨(⟨x,Finset.mem_filter.mpr ⟨hxB,hxO⟩⟩,reverse e.val.2),?_⟩
  rw [step_reverse]
  simpa only [x,add_neg_cancel_right] using (show inBox N (site e.val.1) from fun i => (e.val.1 i).property)

/-- A once-per-copy bijection; several exits at the same active site remain distinct. -/
def exitEquiv (N : ℕ) : ExteriorIncidence N ≃ ExitEdge N where
  toFun := toExit N
  invFun := fromExit N
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      simp only [fromExit,toExit,site_activeOfSite,step_reverse,add_neg_cancel_right]
    · exact reverse_reverse p.val.2
  right_inv e := by
    apply Subtype.ext
    apply Prod.ext
    · apply site_injective N
      simp only [toExit,fromExit,site_activeOfSite,step_reverse,add_neg_cancel_right]
    · exact reverse_reverse e.val.2

/-- The physical exterior flux counts each retained original wired exit once. -/
theorem conductance_eq_exit_sum (N : ℕ) (S : Finset (Active N)) :
    wiredConductance N S = ∑ e : ExitEdge N, (1-voltage N S (some e.val.1)) := by
  rw [wiredConductance_eq_flux,laplacian,Fintype.sum_sum_type]
  have hs := (voltage_spec N S).1
  simp only [endpoints,Option.some_ne_none,if_false,if_true,add_zero,zero_add,
    Finset.sum_const_zero,hs]

/-- The reversed voltage is nonnegative on the full original lattice. -/
theorem reverse_potential_nonneg (N : ℕ) (S : Finset (Active N)) (x : Site 2) :
    0 ≤ 1-potential N S x := by
  have hs := voltage_spec N S
  have hu := le_of_harmonic (fun e : Edge N => (endpoints e).1)
    (fun e => (endpoints e).2) (terminals N S) (terminals_reachable N S)
    (voltage N S) 1 (by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hs.1.le
      · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
        rw [hs.2.1 y hy]
        exact zero_le_one) hs.2.2
  exact sub_nonneg.mpr (hu (wiredVertex N x))

/-- Restrict the full exterior neighbor sum to its original active incidences. -/
theorem exterior_sum_eq_incidence (N : ℕ) (f : Site 2 → ℝ)
    (hf : ∀ y, ¬inBox N y → f y = 0) :
    (∑ x ∈ outerSites N, ∑ y ∈ nbrFinset x, f y) =
      ∑ p : ExteriorIncidence N, f (p.val.1.val+step p.val.2) := by
  calc
    _ = ∑ x ∈ outerSites N, ∑ d : Direction, f (x+step d) := by
      apply Finset.sum_congr rfl
      intro x _
      exact sum_neighbors x f
    _ = ∑ x : ↥(outerSites N), ∑ d : Direction, f (x.val+step d) :=
      (Finset.sum_coe_sort (outerSites N) (fun x => ∑ d : Direction, f (x+step d))).symm
    _ = ∑ p : ↥(outerSites N) × Direction, f (p.1.val+step p.2) :=
      (Fintype.sum_prod_type (fun p : ↥(outerSites N) × Direction => f (p.1.val+step p.2))).symm
    _ = ∑ p : ↥(outerSites N) × Direction,
        if inBox N (p.1.val+step p.2) then f (p.1.val+step p.2) else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : inBox N (p.1.val+step p.2)
      · rw [if_pos hp]
      · rw [if_neg hp,hf _ hp]
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (fun _ => by simp only [Finset.mem_filter,Finset.mem_univ,true_and]) _

/-- Reindex the actual directed exterior incidences by distinct wired exit-copy IDs. -/
theorem incidence_sum_eq_exit (N : ℕ) (S : Finset (Active N)) :
    (∑ p : ExteriorIncidence N, (1-potential N S (p.val.1.val+step p.val.2))) =
      ∑ e : ExitEdge N, (1-voltage N S (some e.val.1)) := by
  apply Fintype.sum_equiv (exitEquiv N)
  intro p
  change 1-potential N S (p.val.1.val+step p.val.2) =
    1-voltage N S (some (activeOfSite N (p.val.1.val+step p.val.2) p.property))
  rw [potential,wiredVertex,dif_pos p.property]

/-- The full exterior neighbor sum equals the once-per-original-copy conductance. -/
theorem exterior_sum_eq_conductance (N : ℕ) (S : Finset (Active N)) :
    (∑ x ∈ outerSites N, ∑ y ∈ nbrFinset x, (1-potential N S y)) = wiredConductance N S := by
  rw [exterior_sum_eq_incidence N (fun y => 1-potential N S y) (by
    intro y hy
    rw [potential_exterior N S y (fun h => hy ((inBox_iff N y).mpr h)),sub_self]),
    incidence_sum_eq_exit,← conductance_eq_exit_sum]

end
end LocalAnnulusCopies
