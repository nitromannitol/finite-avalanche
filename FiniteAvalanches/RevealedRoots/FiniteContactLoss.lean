import FiniteAvalanches.Needle.Statement
import FiniteAvalanches.Sandpile.Components.Incident
import FiniteAvalanches.Electrical.Response

namespace FiniteAvalanches.RevealedRoots
open LatticeProb FiniteAvalanches.Sandpile.FiniteWired
open FiniteAvalanches.Needle FiniteAvalanches.Electrical
open scoped BigOperators Classical
noncomputable section

/-- The literal contraction of the exterior to the wired terminal. -/
def wiredVertex (N : ℕ) (x : Site 2) : Vertex N :=
  if hx : inBox N x then some (activeOfSite N x hx) else none

/-- Unit Dirichlet voltage on the lattice, with its prescribed exterior value. -/
def potential (N : ℕ) (S : Finset (Active N)) (x : Site 2) : ℝ :=
  voltage N S (wiredVertex N x)

@[simp] theorem wiredVertex_site (N : ℕ) (x : Active N) :
    wiredVertex N (site x) = some x := by
  have hx : inBox N (site x) := fun i => (x i).property
  rw [wiredVertex, dif_pos hx]
  congr 1

@[simp] theorem potential_site (N : ℕ) (S : Finset (Active N)) (x : Active N) :
    potential N S (site x) = voltage N S (some x) := by
  rw [potential, wiredVertex_site]

 theorem potential_exterior (N : ℕ) (S : Finset (Active N)) (x : Site 2)
    (hx : x ∉ box 2 N) : potential N S x = 1 := by
  rw [potential, wiredVertex, dif_neg (fun h => hx ((inBox_iff _ _).mp h))]
  exact (voltage_spec N S).1

private def other (N : ℕ) (x : Active N) (e : Edge N) : Vertex N :=
  if (endpoints e).1 = some x then (endpoints e).2 else (endpoints e).1

private theorem other_direction (N : ℕ) (x : Active N) (d : Direction) :
    other N x (directionEdge x d) = wiredVertex N (site x + step d) := by
  rcases d with ⟨i,b⟩
  cases b
  · simp only [step, Bool.false_eq_true, if_false, ← sub_eq_add_neg]
    by_cases hb : inBox N (site x - unit i)
    · have hn := endpoints_ne (directionEdge x (i,false))
      simp only [directionEdge, dif_pos hb, endpoints] at hn
      simp only [other, directionEdge, endpoints, wiredVertex, dif_pos hb, if_neg hn]
    · simp only [other, directionEdge, endpoints, wiredVertex, dif_neg hb, if_true]
  · simp only [step, if_true]
    by_cases hb : inBox N (site x + unit i)
    · simp only [other, directionEdge, endpoints, wiredVertex, dif_pos hb, if_true]
    · simp only [other, directionEdge, endpoints, wiredVertex, dif_neg hb, if_true]

 theorem neighbors_eq_directions (x : Site 2) :
    nbrFinset x = Finset.univ.image (fun d : Direction => x + step d) := by
  ext y
  simp only [nbrFinset, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton, Finset.mem_image]
  constructor
  · rintro ⟨i, h | h⟩
    · exact ⟨(i,true), by simpa [step] using h.symm⟩
    · exact ⟨(i,false), by simpa [step, sub_eq_add_neg] using h.symm⟩
  · rintro ⟨⟨i,b⟩, h⟩
    cases b
    · exact ⟨i, Or.inr (by simpa [step, sub_eq_add_neg] using h.symm)⟩
    · exact ⟨i, Or.inl (by simpa [step] using h.symm)⟩

 theorem sum_neighbors (x : Site 2) (f : Site 2 → ℝ) :
    (∑ y ∈ nbrFinset x, f y) = ∑ d : Direction, f (x + step d) := by
  rw [neighbors_eq_directions, Finset.sum_image]
  intro d _ e _ h
  exact step_injective (add_left_cancel h)

/-- Positive copied-edge Laplacian, reindexed by every original direction once. -/
theorem laplacian_directions (N : ℕ) (f : Vertex N → ℝ) (x : Active N) :
    laplacian (fun e : Edge N => (endpoints e).1) (fun e => (endpoints e).2) f (some x) =
      ∑ d : Direction, (f (some x) - f (wiredVertex N (site x + step d))) := by
  let I : Finset (Edge N) := Finset.univ.filter (Sandpile.Components.incident x)
  let g : Edge N → ℝ := fun e =>
    (if (endpoints e).1 = some x then f (some x)-f (endpoints e).2 else 0) +
    (if (endpoints e).2 = some x then f (some x)-f (endpoints e).1 else 0)
  have him : I = Finset.univ.image (directionEdge x) := by
    ext e
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · exact Sandpile.Components.exists_direction_of_incident x e
    · rintro ⟨d,rfl⟩
      exact Sandpile.Components.direction_edge_incident x d
  have hz (e : Edge N) (he : e ∉ I) : g e = 0 := by
    have h : ¬Sandpile.Components.incident x e := by simpa [I] using he
    simp only [Sandpile.Components.incident, not_or] at h
    simp only [g, if_neg h.1, if_neg h.2, add_zero]
  have hp (e : Edge N) (he : e ∈ I) : g e = f (some x)-f (other N x e) := by
    have h : Sandpile.Components.incident x e := (Finset.mem_filter.mp he).2
    rcases h with h | h
    · have hn : (endpoints e).2 ≠ some x := fun hh => endpoints_ne e (h.trans hh.symm)
      simp only [g, other, h, if_true, if_neg hn, add_zero]
    · have hn : (endpoints e).1 ≠ some x := fun hh => endpoints_ne e (hh.trans h.symm)
      simp only [g, other, h, if_true, if_neg hn, zero_add]
  have heq : laplacian (fun e : Edge N => (endpoints e).1)
      (fun e => (endpoints e).2) f (some x) = ∑ e : Edge N, g e := by
    unfold laplacian
    apply Finset.sum_congr rfl
    intro e _
    dsimp only [g]
    split_ifs <;> rfl
  rw [heq]
  calc
    _ = ∑ e ∈ I, g e :=
      (Finset.sum_subset (s₁ := I) (s₂ := Finset.univ) (f := g)
        (Finset.subset_univ I) (fun e _ he => hz e he)).symm
    _ = ∑ e ∈ I, (f (some x)-f (other N x e)) := Finset.sum_congr rfl hp
    _ = ∑ d : Direction, (f (some x)-f (other N x (directionEdge x d))) := by
      rw [him, Finset.sum_image]
      exact fun d _ e _ h => Sandpile.Components.direction_edge_injective x h
    _ = _ := Finset.sum_congr rfl (fun d _ => by rw [other_direction])

/-- The literal finite-box voltage satisfies the four-neighbor mean equation. -/
theorem potential_harmonic (N : ℕ) (S : Finset (Active N)) (x : Active N)
    (hx : x ∉ S) : (∑ y ∈ nbrFinset (site x), potential N S y) =
      4 * potential N S (site x) := by
  have h := (voltage_spec N S).2.2 (some x) (by simp [terminals, hx])
  rw [laplacian_directions, Finset.sum_sub_distrib] at h
  have hc : Fintype.card Direction = 4 := by decide
  simp only [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul, Nat.cast_ofNat] at h
  rw [sum_neighbors, potential_site]
  exact (sub_eq_zero.mp h).symm

 theorem potential_nonneg (N : ℕ) (S : Finset (Active N)) (x : Site 2) :
    0 ≤ potential N S x := by
  exact harmonicExtension_nonneg _ _ (terminals N S) (terminals_reachable N S)
    (fun v => if v = none then 1 else 0) (fun v _ => by split_ifs <;> norm_num) _

/-- More zero roots decrease the unit exterior voltage throughout the actual box. -/
theorem potential_antitone (N : ℕ) {S T : Finset (Active N)} (hST : S ⊆ T)
    (x : Site 2) : potential N T x ≤ potential N S x := by
  let a := fun e : Edge N => (endpoints e).1
  let b := fun e : Edge N => (endpoints e).2
  have hS := voltage_spec N S
  have hT := voltage_spec N T
  have hn (v : Vertex N) : 0 ≤ voltage N S v :=
    harmonicExtension_nonneg a b (terminals N S) (terminals_reachable N S)
      (fun v => if v = none then 1 else 0) (fun v _ => by split_ifs <;> norm_num) v
  have h := le_of_harmonic a b (terminals N T) (terminals_reachable N T)
    (voltage N T - voltage N S) 0
    (by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · simp only [Pi.sub_apply, hT.1, hS.1, sub_self, le_refl]
      · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
        simp only [Pi.sub_apply, hT.2.1 y hy, zero_sub]
        exact neg_nonpos.mpr (hn _))
    (by
      intro v hv
      have hvS : v ∉ terminals N S := by
        intro hm
        apply hv
        rcases Finset.mem_insert.mp hm with rfl | hm
        · exact Finset.mem_insert_self _ _
        · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hm
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (hST hy))
      rw [laplacian_sub, hT.2.2 v hv, hS.2.2 v hvS, sub_self])
  have hx := h (wiredVertex N x)
  exact sub_nonpos.mp hx

/-- Literal lattice neighbor sum at all zero vertices equals physical conductance. -/
theorem zero_contact_sum_eq_conductance (N : ℕ) (S : Finset (Active N)) :
    (∑ x ∈ S, ∑ y ∈ nbrFinset (site x), potential N S y) = wiredConductance N S := by
  let a := fun e : Edge N => (endpoints e).1
  let b := fun e : Edge N => (endpoints e).2
  let u := voltage N S
  have hs := voltage_spec N S
  have hx (x : Active N) (hx : x ∈ S) :
      (∑ y ∈ nbrFinset (site x), potential N S y) = -laplacian a b u (some x) := by
    rw [sum_neighbors]
    rw [laplacian_directions]
    simp only [u, hs.2.1 x hx, zero_sub, potential, Finset.sum_neg_distrib, neg_neg]
  have hh : (∑ x : Active N, laplacian a b u (some x)) =
      ∑ x ∈ S, laplacian a b u (some x) := by
    exact (Finset.sum_subset (Finset.subset_univ S) (fun x _ hx =>
      hs.2.2 (some x) (by simp [terminals, hx]))).symm
  have hc := sum_laplacian_eq_zero a b u
  rw [Fintype.sum_option, hh] at hc
  rw [Finset.sum_congr rfl hx, Finset.sum_neg_distrib, wiredConductance_eq_flux]
  linarith only [hc]

/-- Added zero roots are precisely Z\K, even when K extends outside the wired box. -/
def addedZero (h L : ℕ) (p : InBoxVertices h L) (K : Finset Point) : Finset (Active (2*h)) :=
  (zeroVertices h L p).filter (fun x => site x ∉ K)

def enlargedZero (h L : ℕ) (p : InBoxVertices h L) (K : Finset Point) : Finset (Active (2*h)) :=
  zeroVertices h L p ∪ Finset.univ.filter (fun x => site x ∈ K)

 theorem addedZero_image (h L : ℕ) (p : InBoxVertices h L) (K : Finset Point) :
    (addedZero h L p K).image site = target h L p.val \ K := by
  ext y
  simp only [addedZero, Finset.mem_image, Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨x,⟨hx,hK⟩,rfl⟩
    exact ⟨(Finset.mem_filter.mp hx).2,hK⟩
  · rintro ⟨hy,hK⟩
    have hi : y ∈ (zeroVertices h L p).image site := by rw [zeroVertices_image]; exact hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hi
    exact ⟨x,⟨hx,hK⟩,rfl⟩

 theorem added_contact_sum_le_conductance (h L : ℕ) (p : InBoxVertices h L) (K : Finset Point) :
    (∑ x ∈ addedZero h L p K, ∑ y ∈ nbrFinset (site x),
      potential (2*h) (enlargedZero h L p K) y) ≤ wiredConductance (2*h) (zeroVertices h L p) := by
  calc
    _ ≤ ∑ x ∈ addedZero h L p K, ∑ y ∈ nbrFinset (site x),
        potential (2*h) (zeroVertices h L p) y := by
      apply Finset.sum_le_sum
      intro x _
      exact Finset.sum_le_sum (fun y _ => potential_antitone _ Finset.subset_union_left y)
    _ ≤ ∑ x ∈ zeroVertices h L p, ∑ y ∈ nbrFinset (site x),
        potential (2*h) (zeroVertices h L p) y := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun x _ _ => Finset.sum_nonneg (fun y _ => potential_nonneg _ _ y))
    _ = _ := zero_contact_sum_eq_conductance _ _

/-- Exact transport to the paper's original lattice-site contact sum. -/
theorem added_contact_sum_sites (h L : ℕ) (p : InBoxVertices h L) (K : Finset Point) :
    (∑ x ∈ target h L p.val \ K, ∑ y ∈ nbrFinset x,
      potential (2*h) (enlargedZero h L p K) y) =
    ∑ x ∈ addedZero h L p K, ∑ y ∈ nbrFinset (site x),
      potential (2*h) (enlargedZero h L p K) y := by
  rw [← addedZero_image, Finset.sum_image]
  exact fun x _ y _ hxy => site_injective (2*h) hxy

/-- A literal simple needle controls the full added-root contact sum uniformly in K. -/
theorem exists_needle_added_contact_bound (h : ℕ) (hh : 10 ≤ h) (z : Point)
    (hz : Needle.radius z = 2*h) (K : Finset Point) :
    ∃ (L : ℕ) (p : InBoxVertices h L),
      Function.Injective p.val ∧ p.val ⟨0, by omega⟩ ∈ box 2 h ∧
      p.val ⟨L, by omega⟩ = z ∧
      (∀ t : Fin L, (lattice 2).Adj (p.val ⟨t.val, by omega⟩) (p.val ⟨t.val+1, by omega⟩)) ∧
      (∑ x ∈ target h L p.val \ K, ∑ y ∈ nbrFinset x,
        potential (2*h) (enlargedZero h L p K) y) ≤ 3840*Real.log (h+2) := by
  obtain ⟨L,p,hi,hb,he,ha,_,hc⟩ := needle h hh z hz
  refine ⟨L,p,hi,hb,he,ha,?_⟩
  rw [added_contact_sum_sites]
  exact (added_contact_sum_le_conductance h L p K).trans hc

end
end FiniteAvalanches.RevealedRoots

#print axioms FiniteAvalanches.RevealedRoots.laplacian_directions
#print axioms FiniteAvalanches.RevealedRoots.potential_antitone
#print axioms FiniteAvalanches.RevealedRoots.zero_contact_sum_eq_conductance
#print axioms FiniteAvalanches.RevealedRoots.exists_needle_added_contact_bound
