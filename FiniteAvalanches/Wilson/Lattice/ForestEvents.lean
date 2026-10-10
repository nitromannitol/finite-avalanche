import FiniteAvalanches.Wilson.Lattice.ColoredForests
import FiniteAvalanches.Wilson.Lattice.Paths
import FiniteAvalanches.Sandpile.WiredTermination

/-! Literal source contact counts. Every lattice neighbor is counted, including
edges absent from the forest. Real windows retain their real radius. -/
namespace FiniteAvalanches.Wilson.Lattice
open LatticeProb FiniteAvalanches.Sandpile MeasureTheory
open scoped Classical
noncomputable section

/-- The paper's actual finite connected set and genuinely infinite outgoing path. -/
structure ConnectingPair where
  sites : Finset (Site 2)
  ray : SimpleRay
  connected : ((lattice 2).induce (sites : Set (Site 2))).Connected
  ray_mem_iff : ∀ n, ray.vertex n ∈ sites ↔ n = 0

def ConnectingPair.roots (p : ConnectingPair) : RootPair where
  zero := p.sites
  one := p.ray.tailVertices
  disjoint := Set.disjoint_left.mpr (by
    rintro x hx ⟨n, hn⟩
    change p.ray.vertex (n + 1) = x at hn
    have hmem : p.ray.vertex (n + 1) ∈ p.sites := hn.symm ▸ hx
    have he := (p.ray_mem_iff (n + 1)).mp hmem
    omega)
  zero_nonempty := ⟨p.ray.vertex 0, (p.ray_mem_iff 0).mpr rfl⟩
  one_nonempty := p.ray.tail_nonempty

/-- L(K,gamma): the forest itself is deliberately absent from this sum. -/
def contacts (K : Finset (Site 2)) (σ : ColorField) : ℕ :=
  ∑ x ∈ K, ∑ y ∈ nbrFinset x, if σ y then 1 else 0

/-- Exactly the finite sites whose colors occur in the contact count. -/
def contactSites (K : Finset (Site 2)) : Finset (Site 2) :=
  K.biUnion nbrFinset

theorem contacts_of_agree (K : Finset (Site 2)) {σ τ : ColorField}
    (h : ∀ y ∈ contactSites K, σ y = τ y) : contacts K σ = contacts K τ := by
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [h y (Finset.mem_biUnion.mpr ⟨x, hx, hy⟩)]

theorem continuous_contacts (K : Finset (Site 2)) : Continuous (contacts K) := by
  unfold contacts
  exact continuous_finsetSum _ (fun x _ => continuous_finsetSum _ (fun y _ =>
    (continuous_of_discreteTopology : Continuous (fun b : Bool => if b then (1 : ℕ) else 0)).comp
      (continuous_apply y)))

def contactEvent (K : Finset (Site 2)) (t : ℝ) : Set ColorField :=
  {σ | t ≤ (contacts K σ : ℝ)}

theorem isClopen_contactEvent (K : Finset (Site 2)) (t : ℝ) :
    IsClopen (contactEvent K t) :=
  (isClopen_discrete {n : ℕ | t ≤ (n : ℝ)}).preimage (continuous_contacts K)

theorem measurableSet_contactEvent (K : Finset (Site 2)) (t : ℝ) :
    MeasurableSet (contactEvent K t) := (isClopen_contactEvent K t).isClosed.measurableSet

/-- The literal translated integer square B_r(a). -/
def window (a : Site 2) (r : ℕ) : Finset (Site 2) :=
  (boxSites r).image (fun x => a + x)

theorem mem_window (a x : Site 2) (r : ℕ) :
    x ∈ window a r ↔ siteRadius a x ≤ r := by
  have hi : x ∈ window a r ↔ FiniteWired.inBox r (x - a) := by
    constructor
    · rintro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      simpa using (mem_box_sites r y).mp hy
    · intro hx
      exact Finset.mem_image.mpr ⟨x - a, (mem_box_sites r _).mpr hx, by abel⟩
  rw [hi, siteRadius_le_iff]
  simp only [FiniteWired.inBox, Pi.sub_apply, abs_le]

/-- N_(A,C)(a,r), with arbitrary (possibly infinite) zero root set A. -/
def localContacts (A : Set (Site 2)) (a : Site 2) (r : ℕ) (σ : ColorField) : ℕ :=
  contacts ((window a r).filter (fun x => x ∈ A)) σ

/-- N_K(t), retaining the paper's real window parameter. -/
def kContacts (K : Finset (Site 2)) (t : ℝ) (σ : ColorField) : ℕ :=
  contacts (K.filter (fun x => (siteRadius 0 x : ℝ) ≤ t)) σ

def localContactEvent (A : Set (Site 2)) (a : Site 2) (r : ℕ) (t : ℝ) : Set ColorField :=
  {σ | t ≤ (localContacts A a r σ : ℝ)}

def kContactEvent (K : Finset (Site 2)) (r t : ℝ) : Set ColorField :=
  {σ | t ≤ (kContacts K r σ : ℝ)}

theorem isClopen_localContactEvent (A : Set (Site 2)) (a : Site 2) (r : ℕ) (t : ℝ) :
    IsClopen (localContactEvent A a r t) := isClopen_contactEvent _ t

theorem isClopen_kContactEvent (K : Finset (Site 2)) (r t : ℝ) :
    IsClopen (kContactEvent K r t) := isClopen_contactEvent _ t

/-- The actual first ray edge supplies a contact; no event/probability bound is assumed. -/
theorem contacts_ge_one (p : ConnectingPair) (σ : ColorField)
    (hσ : σ (p.ray.vertex 1) = true) : 1 ≤ contacts p.sites σ := by
  have hx : p.ray.vertex 0 ∈ p.sites := (p.ray_mem_iff 0).mpr rfl
  have hy : p.ray.vertex 1 ∈ nbrFinset (p.ray.vertex 0) :=
    (FiniteWired.mem_neighbors_iff _ _).mpr (p.ray.adjacent 0)
  have hi := Finset.single_le_sum (fun y (_ : y ∈ nbrFinset (p.ray.vertex 0)) =>
    Nat.zero_le (if σ y then 1 else 0)) hy
  have ho := Finset.single_le_sum (fun x (_ : x ∈ p.sites) =>
    Nat.zero_le (∑ y ∈ nbrFinset x, if σ y then 1 else 0)) hx
  simp only [hσ, ↓reduceIte] at hi
  exact hi.trans ho

theorem rooted_contacts_ge_one (p : ConnectingPair) (f : RootedForest p.roots) :
    1 ≤ contacts p.sites (colors p.roots f) :=
  contacts_ge_one p _ (colors_of_one_root p.roots f ⟨0, rfl⟩)

end
end FiniteAvalanches.Wilson.Lattice
