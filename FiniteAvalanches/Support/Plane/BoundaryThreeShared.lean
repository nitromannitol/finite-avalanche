import FiniteAvalanches.Support.Plane.TerminalSpeedTail
import FiniteAvalanches.Support.Plane.BoundaryPairArms
import FiniteAvalanches.Support.Plane.BoundaryFirstComplement

/-!
# Three boundary arms with a shared endpoint

Two accesses to one boundary point and a third access to a distinct boundary
point can be joined by separated arms with prescribed terminal speeds.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- Two accesses with a common endpoint and a disjoint third access admit
three rooted arms with their terminal parametrizations preserved. -/
theorem exists_three_boundary_arms_of_shared_endpoint
    {U S : Set (ℝ × ℝ)} {a b c d f : ℝ × ℝ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (p : Path a b) (q : Path c b) (s : Path d f)
    (hp : Function.Injective p) (hq : Function.Injective q) (hs : Function.Injective s)
    (hpq : Disjoint (range p ∩ U) (range q))
    (hps : Disjoint (range p) (range s)) (hqs : Disjoint (range q) (range s))
    (hpU : ∀ t : unitInterval, t ≠ 1 → p t ∈ U)
    (hqU : ∀ t : unitInterval, t ≠ 1 → q t ∈ U)
    (hsU : ∀ t : unitInterval, t ≠ 1 → s t ∈ U)
    (hb : b ∉ U) (hf : f ∉ U) (hS : S.Finite)
    (hpS : Disjoint (range p) S) (hqS : Disjoint (range q) S)
    (hsS : Disjoint (range s) S) :
    ∃ r ∈ U, ∃ (v w : Path r b) (z : Path r f),
      Function.Injective v ∧ Function.Injective w ∧ Function.Injective z ∧
      Disjoint (range v) S ∧ Disjoint (range w) S ∧ Disjoint (range z) S ∧
      range v ∩ Uᶜ = {b} ∧ range w ∩ Uᶜ = {b} ∧ range z ∩ Uᶜ = {f} ∧
      range v ∩ range w = {r, b} ∧ range v ∩ range z = {r} ∧ range w ∩ range z = {r} ∧
      (∃ t : unitInterval, t ≠ 1 ∧ ∀ (u : unitInterval)
        (hu : ((t : ℝ) + 1) / 2 ≤ (u : ℝ)),
        v u = p ⟨2 * (u : ℝ) - 1, by constructor <;> linarith [t.property.1, u.property.2]⟩) ∧
      (∃ t : unitInterval, t ≠ 1 ∧ ∀ (u : unitInterval)
        (hu : ((t : ℝ) + 1) / 2 ≤ (u : ℝ)),
        w u = q ⟨2 * (u : ℝ) - 1, by constructor <;> linarith [t.property.1, u.property.2]⟩) ∧
      (∃ t : unitInterval, t ≠ 1 ∧ ∀ (u : unitInterval)
        (hu : ((t : ℝ) + 1) / 2 ≤ (u : ℝ)),
        z u = s ⟨2 * (u : ℝ) - 1, by constructor <;> linarith [t.property.1, u.property.2]⟩) := by
  let W := U \ range s
  have hW : IsOpen W := hU.sdiff (isCompact_range s.continuous).isClosed
  have hWconn : IsPreconnected W := isPreconnected_sdiff_boundary_path hU hconn s hs hsU hf
  have hpW : ∀ t : unitInterval, t ≠ 1 → p t ∈ W := by
    intro t ht
    exact ⟨hpU t ht, fun h => disjoint_left.mp hps ⟨t, rfl⟩ h⟩
  have hqW : ∀ t : unitInterval, t ≠ 1 → q t ∈ W := by
    intro t ht
    exact ⟨hqU t ht, fun h => disjoint_left.mp hqs ⟨t, rfl⟩ h⟩
  obtain ⟨x, hxW, v, w, hv, hw, hvS, hwS, hvw, hvW, hwW, hvt, hwt⟩ :=
    exists_two_boundary_arms_of_disjoint_inside hW hWconn p q hp hq
      (hpq.mono_left (inter_subset_inter_right _ sdiff_subset)) hpW hqW
      (fun h => hb h.1) (fun h => hb h.1) hS hpS hqS
  have hmeet : range v ∩ range w = {x, b} := by
    apply subset_antisymm
    · intro z hz
      rcases hvw z hz with h | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr h
    · simp only [insert_subset_iff, singleton_subset_iff]
      exact ⟨⟨v.source_mem_range, w.source_mem_range⟩,
        ⟨v.target_mem_range, w.target_mem_range⟩⟩
  let paths : Unit → Path d f := fun _ => s
  have hxS : x ∉ S := fun h => disjoint_left.mp hvS v.source_mem_range h
  have hroot : x ∈ (U \ (⋃ i ∈ ({()} : Finset Unit), range (paths i))) \ S := by
    refine ⟨⟨hxW.1, ?_⟩, hxS⟩
    intro h
    obtain ⟨_, _, h⟩ := mem_iUnion₂.mp h
    exact hxW.2 h
  obtain ⟨access, haccess, haccessS, haccessboundary, _, t, ht, htail⟩ :=
    exists_path_to_boundary_avoiding_paths_disjoint_inside_and_finite
      hU hconn ({()} : Finset Unit) paths (by simpa [paths] using hs) (by simp)
      (by simpa [paths] using hsU) (by simpa [paths] using hf)
      hS (by simpa [paths] using hsS) hroot (i := ()) (by simp)
  have hfb : f ≠ b := fun h => disjoint_left.mp hps (h.symm ▸ p.target_mem_range) s.target_mem_range
  have hfK : f ∉ range v ∪ range w := by
    rintro (h | h)
    · have h' : f ∈ ({b} : Set (ℝ × ℝ)) := hvW ▸ ⟨h, fun hw => hf hw.1⟩
      exact hfb (mem_singleton_iff.mp h')
    · have h' : f ∈ ({b} : Set (ℝ × ℝ)) := hwW ▸ ⟨h, fun hw => hf hw.1⟩
      exact hfb (mem_singleton_iff.mp h')
  have hbAccess : b ∉ range access := by
    intro h
    have h' : b ∈ ({f} : Set (ℝ × ℝ)) := haccessboundary ▸ ⟨h, hb⟩
    exact hfb (mem_singleton_iff.mp h').symm
  obtain ⟨tv, htv, hvspeed⟩ := hvt
  obtain ⟨tw, htw, hwspeed⟩ := hwt
  have hrev : Function.Injective access.symm :=
    haccess.comp unitInterval.symm_involutive.injective
  obtain ⟨r, v', w', z, hv', hw', hz, hvK, hwK, hzAccess, hvw', hvz, hwz,
      hvtail, hwtail, hztail⟩ :=
    exists_common_endpoint_tripod_of_first_hit v w access.symm p q s hv hw hrev hp hq hs
      hmeet hfK (Or.inl v.source_mem_range)
      (by simpa only [Path.symm_range] using hbAccess)
      ⟨tv, htv, terminal_subpath_subset_of_speed v p tv hvspeed⟩
      ⟨tw, htw, terminal_subpath_subset_of_speed w q tw hwspeed⟩
      ⟨t, ht, by simpa only [Path.symm_range] using htail⟩
  have hrU : r ∈ U := by
    by_contra h
    have h' : r ∈ ({f} : Set (ℝ × ℝ)) := haccessboundary ▸
      ⟨by simpa only [Path.symm_range] using hzAccess z.source_mem_range, h⟩
    exact hfK ((mem_singleton_iff.mp h').symm ▸ hvK v'.source_mem_range)
  have hbound {z : ℝ × ℝ} (g : Path r z) (hz : z ∉ U)
      (hg : range g ⊆ range v ∪ range w) (hz_eq : z = b) :
      range g ∩ Uᶜ = {z} := by
    subst z
    apply subset_antisymm
    · intro y hy
      rcases hg hy.1 with hyv | hyw
      · exact hvW ▸ ⟨hyv, fun h => hy.2 h.1⟩
      · exact hwW ▸ ⟨hyw, fun h => hy.2 h.1⟩
    · exact singleton_subset_iff.mpr ⟨g.target_mem_range, hz⟩
  have hzU : range z ∩ Uᶜ = {f} := by
    apply subset_antisymm
    · exact (inter_subset_inter_left _ (by simpa only [Path.symm_range] using hzAccess)).trans
        haccessboundary.le
    · exact singleton_subset_iff.mpr ⟨z.target_mem_range, hf⟩
  exact ⟨r, hrU, v', w', z, hv', hw', hz,
    (disjoint_union_left.mpr ⟨hvS, hwS⟩).mono_left hvK,
    (disjoint_union_left.mpr ⟨hvS, hwS⟩).mono_left hwK,
    haccessS.mono_left (by simpa only [Path.symm_range] using hzAccess),
    hbound v' hb hvK rfl, hbound w' hb hwK rfl, hzU,
    hvw', hvz, hwz, hvtail, hwtail, hztail⟩

end FiniteAvalanches.Electrical.StatementGeometry
