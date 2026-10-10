import FiniteAvalanches.Needle.Geometry

open FiniteAvalanches.Sandpile.FiniteWired

namespace FiniteAvalanches.Needle
open LatticeProb
open scoped BigOperators Classical

/-- The full original-copy wired lattice has a path from every vertex to its sink. -/
theorem wired_support_reaches_sink (N : ℕ) (v : Vertex N) :
    (FiniteAvalanches.Electrical.supportGraph (fun e : Edge N => (endpoints e).1)
      (fun e => (endpoints e).2)).Reachable v none := by
  have he : FiniteAvalanches.Electrical.supportGraph (fun e : Edge N => (endpoints e).1)
      (fun e => (endpoints e).2) = (FiniteAvalanches.Sandpile.WiredTrees.graph N).toSimple Finset.univ := by
    apply SimpleGraph.ext
    funext x y
    apply propext
    change (x ≠ y ∧ ∃ e : Edge N,
      ((endpoints e).1 = x ∧ (endpoints e).2 = y) ∨
      ((endpoints e).2 = x ∧ (endpoints e).1 = y)) ↔
      (∃ e : Edge N, e ∈ Finset.univ ∧
      (((endpoints e).1 = x ∧ (endpoints e).2 = y) ∨
      ((endpoints e).2 = x ∧ (endpoints e).1 = y)))
    constructor
    · rintro ⟨_, e, he⟩; exact ⟨e, Finset.mem_univ _, he⟩
    · rintro ⟨e, _, he⟩
      refine ⟨?_, e, he⟩
      intro hxy
      apply endpoints_ne e
      rcases he with ⟨ha, hb⟩ | ⟨hb, ha⟩
      · exact ha.trans (hxy.trans hb.symm)
      · exact ha.trans (hxy.symm.trans hb.symm)
  rw [he, FiniteAvalanches.Trees.Multigraph.toSimple_reachable]
  cases v with
  | none => exact Relation.ReflTransGen.refl
  | some x =>
    apply FiniteAvalanches.Trees.Multigraph.reaches_mono _ (Finset.subset_univ _)
    exact FiniteAvalanches.Sandpile.WiredTrees.row_reaches_sink x

/-- The prescribed zero terminal and the original wired exterior terminal. -/
noncomputable def terminals (N : ℕ) (S : Finset (Active N)) : Finset (Vertex N) :=
  insert none (S.image some)

theorem terminals_reachable (N : ℕ) (S : Finset (Active N)) :
    ∀ x, ∃ y ∈ terminals N S,
      (FiniteAvalanches.Electrical.supportGraph (fun e : Edge N => (endpoints e).1)
        (fun e => (endpoints e).2)).Reachable x y := by
  intro x
  exact ⟨none, Finset.mem_insert_self _ _, wired_support_reaches_sink N x⟩

/-- Unit voltage, characterized by proved existence and uniqueness of the Dirichlet problem. -/
noncomputable def voltage (N : ℕ) (S : Finset (Active N)) : Vertex N → ℝ :=
  FiniteAvalanches.Electrical.harmonicExtension
    (fun e : Edge N => (endpoints e).1) (fun e => (endpoints e).2)
    (terminals N S) (terminals_reachable N S) (fun v => if v = none then 1 else 0)

theorem voltage_spec (N : ℕ) (S : Finset (Active N)) :
    voltage N S none = 1 ∧
      (∀ x ∈ S, voltage N S (some x) = 0) ∧
      (∀ x, x ∉ terminals N S → FiniteAvalanches.Electrical.laplacian
        (fun e : Edge N => (endpoints e).1) (fun e => (endpoints e).2) (voltage N S) x = 0) := by
  have hs := FiniteAvalanches.Electrical.harmonicExtension_spec
    (fun e : Edge N => (endpoints e).1) (fun e => (endpoints e).2)
    (terminals N S) (terminals_reachable N S) (fun v => if v = none then 1 else 0)
  refine ⟨?_, ?_, hs.2⟩
  · simpa [voltage] using hs.1 none (Finset.mem_insert_self _ _)
  · intro x hx
    simpa [voltage] using hs.1 (some x) (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ hx))

theorem voltage_unique (N : ℕ) (S : Finset (Active N)) (f : Vertex N → ℝ)
    (hf0 : f none = 1) (hfS : ∀ x ∈ S, f (some x) = 0)
    (hfH : ∀ v, v ∉ terminals N S → FiniteAvalanches.Electrical.laplacian
      (fun e : Edge N => (endpoints e).1) (fun e => (endpoints e).2) f v = 0) :
    f = voltage N S := by
  apply FiniteAvalanches.Electrical.harmonicExtension_eq
  refine ⟨?_, hfH⟩
  intro v hv
  rcases Finset.mem_insert.mp hv with rfl | hv
  · simpa using hf0
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    simpa using hfS x hx

/-- Effective conductance between `S` and the complement, with every original copy once. -/
noncomputable def wiredConductance (N : ℕ) (S : Finset (Active N)) : ℝ :=
  FiniteAvalanches.Electrical.energy (fun e : Edge N => (endpoints e).1)
    (fun e => (endpoints e).2) (voltage N S)

theorem wiredConductance_le_trial (N : ℕ) (S : Finset (Active N)) (f : Vertex N → ℝ)
    (hf0 : f none = 1) (hfS : ∀ x ∈ S, f (some x) = 0) :
    wiredConductance N S ≤ FiniteAvalanches.Electrical.energy
      (fun e : Edge N => (endpoints e).1) (fun e => (endpoints e).2) f := by
  apply FiniteAvalanches.Electrical.energy_harmonicExtension_le
  intro v hv
  rcases Finset.mem_insert.mp hv with rfl | hv
  · simpa using hf0
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    simpa using hfS x hx

/-- The same quantity is the original-copy unit-voltage current from the exterior terminal. -/
theorem wiredConductance_eq_flux (N : ℕ) (S : Finset (Active N)) :
    wiredConductance N S = FiniteAvalanches.Electrical.laplacian
      (fun e : Edge N => (endpoints e).1) (fun e => (endpoints e).2) (voltage N S) none := by
  obtain ⟨h0, hS, hH⟩ := voltage_spec N S
  rw [wiredConductance, FiniteAvalanches.Electrical.energy_eq_incidence_sum]
  rw [Finset.sum_eq_single none]
  · rw [h0, one_mul]
  · intro v _ hv
    cases v with
    | none => exact (hv rfl).elim
    | some x =>
      by_cases hx : x ∈ S
      · rw [hS x hx, zero_mul]
      · have hvB : some x ∉ terminals N S := by simp [terminals, hx]
        rw [hH (some x) hvB, mul_zero]
  · simp

/-- A finite ordered family of vertices in the source outer box. -/
abbrev InBoxVertices (h L : ℕ) :=
  {p : Fin (L+1) → Point // ∀ t, p t ∈ box 2 (2*h)}

/-- The complete box/path union on the canonical active carrier. -/
noncomputable def zeroVertices (h L : ℕ) (p : InBoxVertices h L) : Finset (Active (2*h)) :=
  Finset.univ.filter (fun x => site x ∈ target h L p.val)

theorem zeroVertices_image (h L : ℕ) (p : InBoxVertices h L) :
    (zeroVertices h L p).image site = target h L p.val := by
  ext x
  constructor
  · rintro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hy).2
  · intro hx
    have hxB : x ∈ box 2 (2*h) := by
      rcases Finset.mem_union.mp hx with hb | hpath
      · have hb := (mem_boxPoints h x).mp hb
        intro i; have hi := hb i; omega
      · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hpath
        exact p.property t
    let y := activeOfSite (2*h) x ((inBox_iff _ _).mpr hxB)
    exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩

end FiniteAvalanches.Needle
