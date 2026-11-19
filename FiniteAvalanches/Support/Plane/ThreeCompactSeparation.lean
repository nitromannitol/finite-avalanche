import FiniteAvalanches.Support.Plane.TopoJaniszewski

/-!
# Joining compact plane sets without creating separation

Janiszewski's theorem applied twice controls the complement of a union of
three compact sets when each successive intersection is preconnected.
-/

namespace LatticeProb.PlaneTopology

open Set
open QuantumZipper.CA.Topo

/-- If two points remain connected outside a compact set and outside the union
of two other compact sets, then they remain connected outside all three when
the successive intersections are preconnected. -/
theorem connectedComponentIn_compl_union_three
    {A K L : Set ℂ} {a b : ℂ}
    (hA : IsCompact A) (hK : IsCompact K) (hL : IsCompact L)
    (hAK : IsPreconnected (A ∩ K)) (hAKL : IsPreconnected ((A ∪ K) ∩ L))
    (ha : a ∉ (A ∪ K) ∪ L) (hb : b ∉ (A ∪ K) ∪ L)
    (hconnA : b ∈ connectedComponentIn Aᶜ a)
    (hconnKL : b ∈ connectedComponentIn (K ∪ L)ᶜ a) :
    b ∈ connectedComponentIn ((A ∪ K) ∪ L)ᶜ a := by
  have hconnK : b ∈ connectedComponentIn Kᶜ a :=
    connectedComponentIn_mono a (compl_subset_compl.mpr subset_union_left) hconnKL
  have hconnL : b ∈ connectedComponentIn Lᶜ a :=
    connectedComponentIn_mono a (compl_subset_compl.mpr subset_union_right) hconnKL
  have haAK : a ∉ A ∪ K := fun h => ha (Or.inl h)
  have hbAK : b ∉ A ∪ K := fun h => hb (Or.inl h)
  have hconnAK : b ∈ connectedComponentIn (A ∪ K)ᶜ a :=
    janiszewski hA hK hAK haAK hbAK hconnA hconnK
  exact janiszewski (hA.union hK) hL hAKL ha hb hconnAK hconnL

end LatticeProb.PlaneTopology
