import FiniteAvalanches.Wilson.Lattice.ForestEvents

set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice
open LatticeProb

/-- prepend the vertex `k` to the ray `γ`. -/
def SimpleRay.prepend (γ : SimpleRay) (k : Site 2) (hadj : (lattice 2).Adj k (γ.vertex 0))
    (hfree : k ∉ γ.vertices) : SimpleRay where
  vertex := fun
    | 0 => k
    | n + 1 => γ.vertex n
  adjacent := by
    intro n
    cases n with
    | zero => exact hadj
    | succ n => exact γ.adjacent n
  injective := by
    intro a b hab
    rcases a with _ | a <;> rcases b with _ | b
    · rfl
    · have h : k = γ.vertex b := hab
      exact (hfree ⟨b, h.symm⟩).elim
    · have h : γ.vertex a = k := hab
      exact (hfree ⟨a, h⟩).elim
    · have h : γ.vertex a = γ.vertex b := hab
      exact congrArg (· + 1) (γ.injective h)

theorem SimpleRay.prepend_vertices (γ : SimpleRay) (k : Site 2)
    (hadj : (lattice 2).Adj k (γ.vertex 0)) (hfree : k ∉ γ.vertices) :
    (γ.prepend k hadj hfree).vertices = insert k γ.vertices := by
  ext x
  rw [Set.mem_insert_iff]
  constructor
  · rintro ⟨n, rfl⟩
    cases n with
    | zero => exact Or.inl rfl
    | succ n => exact Or.inr ⟨n, rfl⟩
  · rintro (rfl | ⟨n, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨n + 1, rfl⟩

theorem SimpleRay.prepend_tailVertices (γ : SimpleRay) (k : Site 2)
    (hadj : (lattice 2).Adj k (γ.vertex 0)) (hfree : k ∉ γ.vertices) :
    (γ.prepend k hadj hfree).tailVertices = γ.vertices := rfl

theorem SimpleRay.prepend_union_K (K : Finset (Site 2)) (γ : SimpleRay) (k : Site 2)
    (hk : k ∈ K) (hadj : (lattice 2).Adj k (γ.vertex 0)) (hfree : k ∉ γ.vertices) :
    (K : Set (Site 2)) ∪ (γ.prepend k hadj hfree).vertices =
      (K : Set (Site 2)) ∪ γ.vertices := by
  rw [SimpleRay.prepend_vertices]
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Finset.mem_coe]
  constructor
  · rintro (hx | rfl | hx)
    · exact Or.inl hx
    · exact Or.inl hk
    · exact Or.inr hx
  · rintro (hx | hx)
    · exact Or.inl hx
    · exact Or.inr (Or.inr hx)

/-- the prepended ray as a `ConnectingPair`
over `K`. Its roots are the root data of `ν_{K,γ}`. -/
def prependConnectingPair (K : Finset (Site 2))
    (hK : ((lattice 2).induce (K : Set (Site 2))).Connected)
    (γ : SimpleRay) (k : Site 2) (hk : k ∈ K) (hadj : (lattice 2).Adj k (γ.vertex 0))
    (hfree : ∀ n, γ.vertex n ∉ K) : ConnectingPair where
  sites := K
  ray := γ.prepend k hadj (by
    rintro ⟨n, hn⟩
    exact hfree n (by rw [hn]; exact hk))
  connected := hK
  ray_mem_iff := by
    intro n
    cases n with
    | zero => exact ⟨fun _ => rfl, fun _ => hk⟩
    | succ n =>
      exact ⟨fun h => (hfree n h).elim, fun h => (Nat.succ_ne_zero n h).elim⟩

theorem prependConnectingPair_roots (K : Finset (Site 2))
    (hK : ((lattice 2).induce (K : Set (Site 2))).Connected)
    (γ : SimpleRay) (k : Site 2) (hk : k ∈ K) (hadj : (lattice 2).Adj k (γ.vertex 0))
    (hfree : ∀ n, γ.vertex n ∉ K) :
    (prependConnectingPair K hK γ k hk hadj hfree).roots.zero = (K : Set (Site 2)) ∧
      (prependConnectingPair K hK γ k hk hadj hfree).roots.one = γ.vertices :=
  ⟨rfl, rfl⟩

/-- Diameter-relevant data: the sites are literally `K`, so any function of `K` is unchanged.
The contact count is unchanged for every color field. -/
theorem prependConnectingPair_sites_contacts (K : Finset (Site 2))
    (hK : ((lattice 2).induce (K : Set (Site 2))).Connected)
    (γ : SimpleRay) (k : Site 2) (hk : k ∈ K) (hadj : (lattice 2).Adj k (γ.vertex 0))
    (hfree : ∀ n, γ.vertex n ∉ K) :
    (prependConnectingPair K hK γ k hk hadj hfree).sites = K ∧
      ∀ σ : ColorField,
        contacts (prependConnectingPair K hK γ k hk hadj hfree).sites σ = contacts K σ :=
  ⟨rfl, fun _ => rfl⟩

/-- Root-color consumer: every rooted forest of the reencoded pair colors `γ` one. -/
theorem prependConnectingPair_colors_one (K : Finset (Site 2))
    (hK : ((lattice 2).induce (K : Set (Site 2))).Connected)
    (γ : SimpleRay) (k : Site 2) (hk : k ∈ K) (hadj : (lattice 2).Adj k (γ.vertex 0))
    (hfree : ∀ n, γ.vertex n ∉ K)
    (f : RootedForest (prependConnectingPair K hK γ k hk hadj hfree).roots) {x : Site 2}
    (hx : x ∈ γ.vertices) : colors _ f x = true :=
  colors_of_one_root _ f (by
    rw [(prependConnectingPair_roots K hK γ k hk hadj hfree).2]
    exact hx)

end FiniteAvalanches.Wilson.Lattice
