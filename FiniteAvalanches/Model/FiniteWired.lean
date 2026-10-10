import LatticeProb.Site

/-!
Finite wired square boxes, with individual exit edge copies and forbidden-subset
recurrence. The counting law below is on the literal allowed-height subtype;
its identification with Markov recurrence is a separate literature result.
-/

namespace FiniteAvalanches.Sandpile.FiniteWired

open LatticeProb MeasureTheory
open scoped ENNReal
open scoped Classical

noncomputable section

abbrev Active (N : ℕ) := Fin 2 → Set.Icc (-(N : ℤ)) (N : ℤ)

def site {N : ℕ} (x : Active N) : Site 2 := fun i => (x i).val

theorem site_injective (N : ℕ) : Function.Injective (@site N) := by
  intro x y h
  funext i
  exact Subtype.ext (congrFun h i)

def inBox (N : ℕ) (x : Site 2) : Prop := ∀ i, -(N : ℤ) ≤ x i ∧ x i ≤ N

def activeOfSite (N : ℕ) (x : Site 2) (h : inBox N x) : Active N :=
  fun i => ⟨x i, h i⟩

theorem site_activeOfSite (N : ℕ) (x : Site 2) (h : inBox N x) :
    site (activeOfSite N x h) = x := rfl

theorem inBox_iff (N : ℕ) (x : Site 2) :
    inBox N x ↔ x ∈ box 2 N := by
  simp only [inBox, box, Set.mem_setOf_eq, abs_le]

abbrev Direction := Fin 2 × Bool

def step (d : Direction) : Site 2 := if d.2 then unit d.1 else -unit d.1

theorem step_injective : Function.Injective step := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  fin_cases i <;> fin_cases j <;> cases b <;> cases c
  all_goals norm_num [step, unit, funext_iff, Fin.forall_fin_two] at h
  all_goals rfl

abbrev InteriorEdge (N : ℕ) :=
  {p : Active N × Active N // ∃ i : Fin 2, site p.2 = site p.1 + unit i}

abbrev ExitEdge (N : ℕ) :=
  {p : Active N × Direction // ¬inBox N (site p.1 + step p.2)}

/-- Each internal edge occurs in its positive-coordinate orientation once.
An exit copy remembers both its active endpoint and its outward direction. -/
abbrev Edge (N : ℕ) := InteriorEdge N ⊕ ExitEdge N

abbrev Vertex (N : ℕ) := Option (Active N)

def endpoints {N : ℕ} (e : Edge N) : Vertex N × Vertex N :=
  match e with
  | .inl e => (some e.val.1, some e.val.2)
  | .inr e => (some e.val.1, none)

def conductance {N : ℕ} (_e : Edge N) : ℝ := 1

theorem endpoints_ne {N : ℕ} (e : Edge N) :
    (endpoints e).1 ≠ (endpoints e).2 := by
  cases e with
  | inl e =>
    intro h
    have he : e.val.1 = e.val.2 := Option.some.inj h
    obtain ⟨i, hi⟩ := e.property
    have hh := congrFun hi i
    rw [he] at hh
    simp [unit, site] at hh
  | inr e => simp [endpoints]

abbrev Heights (N : ℕ) := Active N → Fin 4

def internalDegree {N : ℕ} (s : Finset (Active N)) (x : Active N) : ℕ :=
  (nbrFinset (site x) ∩ s.image site).card

theorem mem_neighbors_iff (x y : Site 2) :
    y ∈ nbrFinset x ↔ (lattice 2).Adj x y := by
  change y ∈ nbrFinset x ↔ ∃ i : Fin 2, y = x + unit i ∨ x = y + unit i
  simp only [nbrFinset, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi | hi⟩
    · exact ⟨i, Or.inl hi⟩
    · exact ⟨i, Or.inr (by rw [hi]; abel)⟩
  · rintro ⟨i, hi | hi⟩
    · exact ⟨i, Or.inl hi⟩
    · exact ⟨i, Or.inr (by rw [hi]; abel)⟩

theorem internalDegree_eq_adj_card {N : ℕ} (s : Finset (Active N)) (x : Active N) :
    internalDegree s x = (s.filter (fun y => (lattice 2).Adj (site x) (site y))).card := by
  classical
  have he : nbrFinset (site x) ∩ s.image site =
      (s.filter (fun y => (lattice 2).Adj (site x) (site y))).image site := by
    ext y
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_filter, mem_neighbors_iff]
    constructor
    · rintro ⟨ha, z, hz, rfl⟩
      exact ⟨z, ⟨hz, ha⟩, rfl⟩
    · rintro ⟨z, ⟨hz, ha⟩, rfl⟩
      exact ⟨ha, z, hz, rfl⟩
  rw [internalDegree, he, Finset.card_image_of_injective _ (site_injective N)]

def forbidden {N : ℕ} (η : Heights N) (s : Finset (Active N)) : Prop :=
  s.Nonempty ∧ ∀ x ∈ s, (η x).val < internalDegree s x

def recurrent {N : ℕ} (η : Heights N) : Prop := ∀ s, ¬forbidden η s

def allThree (N : ℕ) : Heights N := fun _ => 3

private theorem card_neighbors (x : Site 2) : (nbrFinset x).card = 4 := by
  classical
  rw [nbrFinset, Finset.card_biUnion]
  · have hc : ∀ i : Fin 2, ({x + unit i, x - unit i} : Finset (Site 2)).card = 2 := by
      intro i
      rw [Finset.card_insert_of_notMem, Finset.card_singleton]
      simp only [Finset.mem_singleton]
      intro h
      have hi := congrFun h i
      simp only [unit, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same] at hi
      omega
    simp [hc]
  · intro i _ j _ hij
    simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    rintro a (rfl | rfl) (h | h) <;>
      have h1 := congrFun h i <;>
      have h2 := congrFun h j <;>
      simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne, hij] at h1 h2

theorem exists_boundary_vertex {N : ℕ} (s : Finset (Active N)) (hs : s.Nonempty) :
    ∃ x ∈ s, internalDegree s x ≤ 3 := by
  classical
  obtain ⟨x, hx, hmax⟩ := s.exists_max_image (fun x => site x 0) hs
  have hout : site x + unit (0 : Fin 2) ∉ s.image site := by
    intro h
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp h
    have hle := hmax y hy
    have he0 := congrFun he 0
    simp [unit] at he0
    omega
  have hsub : nbrFinset (site x) ∩ s.image site ⊂ nbrFinset (site x) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, ?_⟩
    intro he
    have hm : site x + unit (0 : Fin 2) ∈ nbrFinset (site x) := by
      simp only [nbrFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨0, by simp⟩
    rw [← he] at hm
    exact hout (Finset.mem_inter.mp hm).2
  have hc := Finset.card_lt_card hsub
  rw [card_neighbors] at hc
  exact ⟨x, hx, by dsimp [internalDegree]; omega⟩

theorem allThree_recurrent (N : ℕ) : recurrent (allThree N) := by
  intro s hs
  obtain ⟨x, hx, hdeg⟩ := exists_boundary_vertex s hs.1
  have hlt := hs.2 x hx
  change 3 < internalDegree s x at hlt
  omega

abbrev Recurrent (N : ℕ) := {η : Heights N // recurrent η}

instance recurrentNonempty (N : ℕ) : Nonempty (Recurrent N) :=
  ⟨⟨allThree N, allThree_recurrent N⟩⟩

instance recurrentFintype (N : ℕ) : Fintype (Recurrent N) := Fintype.ofFinite _

instance recurrentMeasurableSpace (N : ℕ) : MeasurableSpace (Recurrent N) := ⊤

instance recurrentMeasurableSingletonClass (N : ℕ) :
    MeasurableSingletonClass (Recurrent N) := ⟨fun _ => trivial⟩

/-- Normalized counting measure on all stable fields with no forbidden subset. -/
def law (N : ℕ) : Measure (Recurrent N) :=
  (Fintype.card (Recurrent N) : ℝ≥0∞)⁻¹ • Measure.count

theorem law_singleton (N : ℕ) (η : Recurrent N) :
    law N {η} = (Fintype.card (Recurrent N) : ℝ≥0∞)⁻¹ := by
  simp [law, Measure.smul_apply, smul_eq_mul]

instance lawProbability (N : ℕ) : IsProbabilityMeasure (law N) := by
  constructor
  simp only [law, Measure.smul_apply, smul_eq_mul, Measure.count_univ]
  rw [ENat.card_eq_coe_fintype_card]
  simp [ENNReal.inv_mul_cancel, Fintype.card_ne_zero]

theorem law_apply (N : ℕ) (s : Set (Recurrent N)) :
    law N s = s.encard / Fintype.card (Recurrent N) := by
  rw [law, Measure.smul_apply, smul_eq_mul, Measure.count_apply s.toFinite.measurableSet]
  exact ENNReal.div_eq_inv_mul.symm

/-- Auxiliary zero extension of a finite input field, not an infinite-volume law. -/
def zeroExtend (N : ℕ) (η : Recurrent N) : Site 2 → Fin 4 :=
  fun x => if h : inBox N x then η.val (activeOfSite N x h) else 0

theorem zeroExtend_site (N : ℕ) (η : Recurrent N) (x : Active N) :
    zeroExtend N η (site x) = η.val x := by
  have h : inBox N (site x) := fun i => (x i).property
  rw [zeroExtend, dif_pos h]
  congr 1

theorem zeroExtend_outside (N : ℕ) (η : Recurrent N) (x : Site 2)
    (h : ¬inBox N x) : zeroExtend N η x = 0 := by
  simp only [zeroExtend, dif_neg h]

theorem zeroExtend_measurable (N : ℕ) : Measurable (zeroExtend N) :=
  measurable_of_countable _

/-- Push-forward of the finite recurrent counting law by the specified zero extension. -/
def finiteFieldLaw (N : ℕ) : Measure (Site 2 → Fin 4) :=
  Measure.map (zeroExtend N) (law N)

instance finiteFieldLawProbability (N : ℕ) : IsProbabilityMeasure (finiteFieldLaw N) :=
  Measure.isProbabilityMeasure_map (zeroExtend_measurable N).aemeasurable




end

end FiniteAvalanches.Sandpile.FiniteWired
