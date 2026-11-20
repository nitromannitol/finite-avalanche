import FiniteAvalanches.Support.Plane.BoundaryThreeProtected
import FiniteAvalanches.Support.Plane.BoundaryThreeShared

/-!
# Three boundary accesses with endpoint multiplicity at most two

Three accesses admit separated rooted arms when no boundary point is the
endpoint of all three.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

private theorem separate_of_singleton {X : Type*} {r a b : X} {A B : Set X}
    (h : A ∩ B = {r}) : ∀ z ∈ A ∩ B, z = r ∨ z = a ∧ a = b := by
  intro z hz
  exact Or.inl (mem_singleton_iff.mp (h ▸ hz))

private theorem separate_of_pair {X : Type*} {r a : X} {A B : Set X}
    (h : A ∩ B = {r, a}) : ∀ z ∈ A ∩ B, z = r ∨ z = a ∧ a = a := by
  intro z hz
  have hz' : z ∈ ({r, a} : Set X) := h ▸ hz
  rcases hz' with hz' | hz'
  · exact Or.inl hz'
  · exact Or.inr ⟨hz', rfl⟩

/-- Three accesses with endpoint multiplicity at most two admit separated
arms with prescribed terminal speeds. -/
theorem exists_three_boundary_arms_of_endpoint_multiplicity_le_two
    {U S : Set (ℝ × ℝ)} {a b c d e f : ℝ × ℝ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (p : Path a b) (q : Path c d) (s : Path e f)
    (hp : Function.Injective p) (hq : Function.Injective q) (hs : Function.Injective s)
    (hpq : Disjoint (range p ∩ U) (range q))
    (hps : Disjoint (range p ∩ U) (range s))
    (hqs : Disjoint (range q ∩ U) (range s))
    (hpU : ∀ t : unitInterval, t ≠ 1 → p t ∈ U)
    (hqU : ∀ t : unitInterval, t ≠ 1 → q t ∈ U)
    (hsU : ∀ t : unitInterval, t ≠ 1 → s t ∈ U)
    (hb : b ∉ U) (hd : d ∉ U) (hf : f ∉ U) (hS : S.Finite)
    (hpS : Disjoint (range p) S) (hqS : Disjoint (range q) S)
    (hsS : Disjoint (range s) S) (hthree : ¬ (b = d ∧ b = f)) :
    ∃ r ∈ U, ∃ (v : Path r b) (w : Path r d) (z : Path r f),
      Function.Injective v ∧ Function.Injective w ∧ Function.Injective z ∧
      Disjoint (range v) S ∧ Disjoint (range w) S ∧ Disjoint (range z) S ∧
      range v ∩ Uᶜ = {b} ∧ range w ∩ Uᶜ = {d} ∧ range z ∩ Uᶜ = {f} ∧
      (∀ x ∈ range v ∩ range w, x = r ∨ x = b ∧ b = d) ∧
      (∀ x ∈ range v ∩ range z, x = r ∨ x = b ∧ b = f) ∧
      (∀ x ∈ range w ∩ range z, x = r ∨ x = d ∧ d = f) ∧
      (∃ t : unitInterval, t ≠ 1 ∧ ∀ (u : unitInterval)
        (hu : ((t : ℝ) + 1) / 2 ≤ (u : ℝ)),
        v u = p ⟨2 * (u : ℝ) - 1, by constructor <;> linarith [t.property.1, u.property.2]⟩) ∧
      (∃ t : unitInterval, t ≠ 1 ∧ ∀ (u : unitInterval)
        (hu : ((t : ℝ) + 1) / 2 ≤ (u : ℝ)),
        w u = q ⟨2 * (u : ℝ) - 1, by constructor <;> linarith [t.property.1, u.property.2]⟩) ∧
      (∃ t : unitInterval, t ≠ 1 ∧ ∀ (u : unitInterval)
        (hu : ((t : ℝ) + 1) / 2 ≤ (u : ℝ)),
        z u = s ⟨2 * (u : ℝ) - 1, by constructor <;> linarith [t.property.1, u.property.2]⟩) := by
  have reverse_disjoint {x y : Set (ℝ × ℝ)}
      (h : Disjoint (x ∩ U) y) : Disjoint (y ∩ U) x := by
    apply disjoint_left.mpr
    rintro z ⟨hzy, hzU⟩ hzx
    exact disjoint_left.mp h ⟨hzx, hzU⟩ hzy
  by_cases hbd : b = d
  · subst d
    have hbf : b ≠ f := fun h => hthree ⟨rfl, h⟩
    have hps' := disjoint_boundary_paths_of_ne_targets p s hpU hsU hb hf hps hbf
    have hqs' := disjoint_boundary_paths_of_ne_targets q s hqU hsU hd hf hqs hbf
    obtain ⟨r, hr, v, w, z, hv, hw, hz, hvS, hwS, hzS, hvU, hwU, hzU,
        hvw, hvz, hwz, hvt, hwt, hzt⟩ :=
      exists_three_boundary_arms_of_shared_endpoint hU hconn p q s hp hq hs hpq hps' hqs'
        hpU hqU hsU hb hf hS hpS hqS hsS
    exact ⟨r, hr, v, w, z, hv, hw, hz, hvS, hwS, hzS, hvU, hwU, hzU,
      separate_of_pair hvw, separate_of_singleton hvz, separate_of_singleton hwz,
      hvt, hwt, hzt⟩
  · by_cases hbf : b = f
    · subst f
      have hbd' : b ≠ d := hbd
      have hpq' := disjoint_boundary_paths_of_ne_targets p q hpU hqU hb hd hpq hbd'
      have hsq' := disjoint_boundary_paths_of_ne_targets s q hsU hqU hf hd
        (reverse_disjoint hqs) hbd'
      obtain ⟨r, hr, v, z, w, hv, hz, hw, hvS, hzS, hwS, hvU, hzU, hwU,
          hvz, hvw, hzw, hvt, hzt, hwt⟩ :=
        exists_three_boundary_arms_of_shared_endpoint hU hconn p s q hp hs hq hps hpq' hsq'
          hpU hsU hqU hb hd hS hpS hsS hqS
      exact ⟨r, hr, v, w, z, hv, hw, hz, hvS, hwS, hzS, hvU, hwU, hzU,
        separate_of_singleton hvw, separate_of_pair hvz,
        separate_of_singleton (by simpa only [inter_comm] using hzw), hvt, hwt, hzt⟩
    · by_cases hdf : d = f
      · subst f
        have hdb : d ≠ b := Ne.symm hbd
        have hqp' := disjoint_boundary_paths_of_ne_targets q p hqU hpU hd hb
          (reverse_disjoint hpq) hdb
        have hsp' := disjoint_boundary_paths_of_ne_targets s p hsU hpU hf hb
          (reverse_disjoint hps) hdb
        obtain ⟨r, hr, w, z, v, hw, hz, hv, hwS, hzS, hvS, hwU, hzU, hvU,
            hwz, hwv, hzv, hwt, hzt, hvt⟩ :=
          exists_three_boundary_arms_of_shared_endpoint hU hconn q s p hq hs hp hqs hqp' hsp'
            hqU hsU hpU hd hb hS hqS hsS hpS
        exact ⟨r, hr, v, w, z, hv, hw, hz, hvS, hwS, hzS, hvU, hwU, hzU,
          separate_of_singleton (by simpa only [inter_comm] using hwv),
          separate_of_singleton (by simpa only [inter_comm] using hzv),
          separate_of_pair hwz, hvt, hwt, hzt⟩
      · have hpq' := disjoint_boundary_paths_of_ne_targets p q hpU hqU hb hd hpq hbd
        have hps' := disjoint_boundary_paths_of_ne_targets p s hpU hsU hb hf hps hbf
        have hqs' := disjoint_boundary_paths_of_ne_targets q s hqU hsU hd hf hqs hdf
        obtain ⟨r, hr, v, w, z, hv, hw, hz, hvS, hwS, hzS, hvU, hwU, hzU,
            hvw, hvz, hwz, hvt, hwt, hzt⟩ :=
          exists_three_boundary_arms_of_disjoint_accesses hU hconn p q s hp hq hs hpq' hps' hqs'
            hpU hqU hsU hb hd hf hS hpS hqS hsS
        exact ⟨r, hr, v, w, z, hv, hw, hz, hvS, hwS, hzS, hvU, hwU, hzU,
          separate_of_singleton hvw, separate_of_singleton hvz, separate_of_singleton hwz,
          hvt, hwt, hzt⟩

end FiniteAvalanches.Electrical.StatementGeometry
