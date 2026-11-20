import LatticeProb.Topology.PolygonalArc

/-!
# Simple loops from two arcs

Two simple arcs with common endpoints and otherwise disjoint images concatenate
into a path injective away from its final endpoint.
-/

open Set unitInterval
namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb

/-- Two simple arcs meeting only at their endpoints give a simple loop. -/
theorem path_trans_injOn_of_inter_eq_endpoints {X : Type*} [TopologicalSpace X]
    {a b : X} (p : Path a b) (q : Path b a)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hmeet : range p ∩ range q = {a, b}) :
    InjOn (p.trans q) {t : unitInterval | (t : ℝ) < 1} := by
  intro s hs t ht h
  change (s : ℝ) < 1 at hs
  change (t : ℝ) < 1 at ht
  rw [Path.trans_apply, Path.trans_apply] at h
  split_ifs at h with hs' ht' ht'
  · apply Subtype.ext
    exact mul_left_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0) (congrArg Subtype.val (hp h))
  · have hm : p ⟨2 * s, (mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs'⟩⟩ ∈ ({a, b} : Set X) := by
      rw [← hmeet]
      exact ⟨⟨_, rfl⟩, ⟨_, h.symm⟩⟩
    simp only [mem_insert_iff, mem_singleton_iff] at hm
    rcases hm with ha | hb
    · have hv := hq (h.symm.trans (ha.trans q.target.symm))
      have hv' : 2 * (t : ℝ) - 1 = 1 := congrArg Subtype.val hv
      linarith
    · have hv := hq (h.symm.trans (hb.trans q.source.symm))
      have hv' : 2 * (t : ℝ) - 1 = 0 := congrArg Subtype.val hv
      have ht'' : (t : ℝ) > 1 / 2 := not_le.mp ht'
      linarith
  · have hm : q ⟨2 * s - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.mp hs').le, s.2.2⟩⟩ ∈ ({a, b} : Set X) := by
      rw [← hmeet]
      exact ⟨⟨_, h.symm⟩, ⟨_, rfl⟩⟩
    simp only [mem_insert_iff, mem_singleton_iff] at hm
    rcases hm with ha | hb
    · have hv := hq (ha.trans q.target.symm)
      have hv' : 2 * (s : ℝ) - 1 = 1 := congrArg Subtype.val hv
      linarith
    · have hv := hq (hb.trans q.source.symm)
      have hv' : 2 * (s : ℝ) - 1 = 0 := congrArg Subtype.val hv
      have hs'' : (s : ℝ) > 1 / 2 := not_le.mp hs'
      linarith
  · apply Subtype.ext
    exact mul_left_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0)
      (sub_left_injective (congrArg Subtype.val (hq h)))


/-- Two arcs from the same point to the same crossing determine a simple loop. -/
theorem path_trans_symm_injOn_of_inter_eq_endpoints {X : Type*} [TopologicalSpace X]
    {a b : X} (p q : Path a b)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hmeet : range p ∩ range q = {a, b}) :
    InjOn (p.trans q.symm) {t : unitInterval | (t : ℝ) < 1} := by
  apply path_trans_injOn_of_inter_eq_endpoints p q.symm hp
  · intro s t h
    exact unitInterval.symm_involutive.injective (hq h)
  · simpa only [Path.symm_range] using hmeet

/-- Two root-to-crossing paths assembled from disjoint access paths and terminal
stubs form a simple loop. -/
theorem path_trans_symm_injOn_of_access_paths {X : Type*} [TopologicalSpace X]
    {a b c d : X} (p : Path a c) (q : Path c b) (p' : Path a d) (q' : Path d b)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hp' : Function.Injective p') (hq' : Function.Injective q')
    (hjoin : range p ∩ range q = {c}) (hjoin' : range p' ∩ range q' = {d})
    (haccess : range p ∩ range p' = {a}) (hstubs : range q ∩ range q' = {b})
    (hmix : Disjoint (range p) (range q')) (hmix' : Disjoint (range q) (range p')) :
    InjOn ((p.trans q).trans (p'.trans q').symm)
      {t : unitInterval | (t : ℝ) < 1} := by
  apply path_trans_symm_injOn_of_inter_eq_endpoints
    (p.trans q) (p'.trans q')
    (LatticeProb.Topology.path_trans_injective hp hq hjoin)
    (LatticeProb.Topology.path_trans_injective hp' hq' hjoin')
  rw [Path.trans_range, Path.trans_range, union_inter_distrib_right,
    inter_union_distrib_left, inter_union_distrib_left, haccess, hstubs,
    Set.disjoint_iff_inter_eq_empty.mp hmix, Set.disjoint_iff_inter_eq_empty.mp hmix']
  ext z
  simp only [mem_union, mem_singleton_iff, mem_insert_iff, mem_empty_iff_false,
    or_false, false_or]

/-- Two paths to a crossing stay on their respective sides when joined there. -/
theorem path_trans_symm_mem_sides {X : Type*} [TopologicalSpace X]
    {a b c : X} (p : Path a b) (q : Path c b) {U V : Set X}
    (hp : ∀ t : unitInterval, t ≠ 1 → p t ∈ U)
    (hq : ∀ t : unitInterval, t ≠ 1 → q t ∈ V) :
    (∀ t : unitInterval, (t : ℝ) < 1 / 2 → (p.trans q.symm) t ∈ U) ∧
    (∀ t : unitInterval, 1 / 2 < (t : ℝ) → (p.trans q.symm) t ∈ V) ∧
    (p.trans q.symm) ⟨1 / 2, by norm_num⟩ = b := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rw [Path.trans_apply, dif_pos (le_of_lt ht)]
    apply hp
    intro he
    have hv := congrArg Subtype.val he
    dsimp at hv
    linarith
  · intro t ht
    rw [Path.trans_apply, dif_neg (not_le_of_gt ht)]
    change q (unitInterval.symm _) ∈ V
    apply hq
    intro he
    have hv := congrArg Subtype.val he
    dsimp [unitInterval.symm] at hv
    linarith
  · rw [Path.trans_apply, dif_pos (by norm_num)]
    convert p.target using 1
    congr 1
    apply Subtype.ext
    norm_num

/-- An injective path whose image meets a set only at its source cannot return
to that set. -/
theorem injective_path_avoids_set_after_source {X : Type*} [TopologicalSpace X]
    {a b : X} (p : Path a b) {S : Set X} (hp : Function.Injective p)
    (hmeet : range p ∩ S ⊆ {a}) (t : unitInterval) (ht : t ≠ 0) : p t ∉ S := by
  intro h
  apply ht
  apply hp
  have heq : p t = a := hmeet ⟨⟨t, rfl⟩, h⟩
  simpa only [Path.source] using heq

/-- If two paths meet a vertex set only at their sources, their concatenation
meets that set only at its endpoints. -/
theorem path_trans_symm_mem_vertices {X : Type*} [TopologicalSpace X]
    {a b c : X} (p : Path a b) (q : Path c b) {S : Set X}
    (hp : ∀ t : unitInterval, t ≠ 0 → p t ∉ S)
    (hq : ∀ t : unitInterval, t ≠ 0 → q t ∉ S)
    (t : unitInterval) (ht : (p.trans q.symm) t ∈ S) :
    (t : ℝ) = 0 ∨ (t : ℝ) = 1 := by
  rw [Path.trans_apply] at ht
  split_ifs at ht with h
  · left
    by_contra hn
    apply hp _ ?_ ht
    intro hz
    have hz' := congrArg Subtype.val hz
    dsimp at hz'
    apply hn
    linarith
  · right
    by_contra hn
    apply hq _ ?_ ht
    intro hz
    have hz' := congrArg Subtype.val hz
    dsimp [unitInterval.symm] at hz'
    apply hn
    linarith

/-- Pairwise separation of the halves controls the intersection of joined paths. -/
theorem path_trans_symm_inter_subset {X : Type*} [TopologicalSpace X]
    {a b c a' b' c' : X} (p : Path a b) (q : Path c b)
    (p' : Path a' b') (q' : Path c' b') {S : Set X}
    (hpp : range p ∩ range p' ⊆ S) (hpq : range p ∩ range q' ⊆ S)
    (hqp : range q ∩ range p' ⊆ S) (hqq : range q ∩ range q' ⊆ S) :
    range (p.trans q.symm) ∩ range (p'.trans q'.symm) ⊆ S := by
  rw [Path.trans_range, Path.trans_range, Path.symm_range, Path.symm_range,
    union_inter_distrib_right, inter_union_distrib_left, inter_union_distrib_left]
  exact union_subset (union_subset hpp hpq) (union_subset hqp hqq)

/-- Joined paths whose images intersect only at vertices meet at endpoint
parameters on both paths. -/
theorem path_trans_symm_intersects_at_endpoints {X : Type*} [TopologicalSpace X]
    {a b c a' b' c' : X} (p : Path a b) (q : Path c b)
    (p' : Path a' b') (q' : Path c' b') {S : Set X}
    (hp : ∀ t : unitInterval, t ≠ 0 → p t ∉ S)
    (hq : ∀ t : unitInterval, t ≠ 0 → q t ∉ S)
    (hp' : ∀ t : unitInterval, t ≠ 0 → p' t ∉ S)
    (hq' : ∀ t : unitInterval, t ≠ 0 → q' t ∉ S)
    (hinter : range (p.trans q.symm) ∩ range (p'.trans q'.symm) ⊆ S)
    (s t : unitInterval) (h : (p.trans q.symm) s = (p'.trans q'.symm) t) :
    ((s : ℝ) = 0 ∨ (s : ℝ) = 1) ∧ ((t : ℝ) = 0 ∨ (t : ℝ) = 1) := by
  have hs : (p.trans q.symm) s ∈ S := hinter ⟨⟨s, rfl⟩, ⟨t, h.symm⟩⟩
  exact ⟨path_trans_symm_mem_vertices p q hp hq s hs,
    path_trans_symm_mem_vertices p' q' hp' hq' t (h ▸ hs)⟩

/-- Paths on opposite sides of a trace meet it only at their common endpoint. -/
theorem path_trans_symm_mem_trace_iff {X : Type*} [TopologicalSpace X]
    {a b c : X} (p : Path a b) (q : Path c b) {U V T : Set X}
    (hp : ∀ t : unitInterval, t ≠ 1 → p t ∈ U)
    (hq : ∀ t : unitInterval, t ≠ 1 → q t ∈ V)
    (hU : Disjoint U T) (hV : Disjoint V T) (hb : b ∈ T)
    (t : unitInterval) : (p.trans q.symm) t ∈ T ↔ (t : ℝ) = 1 / 2 := by
  obtain ⟨hleft, hright, hmid⟩ := path_trans_symm_mem_sides p q hp hq
  constructor
  · intro ht
    rcases lt_trichotomy (t : ℝ) (1 / 2) with h | h | h
    · exact (Set.disjoint_left.mp hU (hleft t h) ht).elim
    · exact h
    · exact (Set.disjoint_left.mp hV (hright t h) ht).elim
  · intro ht
    have heq : t = ⟨1 / 2, by norm_num⟩ := Subtype.ext ht
    simpa only [heq, hmid] using hb

/-- An original edge with a unique crossing point meets a glued path exactly there. -/
theorem path_eq_trans_symm_iff {X : Type*} [TopologicalSpace X]
    {a b c : X} (p : Path a b) (q : Path c b) {U V T : Set X}
    (hp : ∀ t : unitInterval, t ≠ 1 → p t ∈ U)
    (hq : ∀ t : unitInterval, t ≠ 1 → q t ∈ V)
    (hU : Disjoint U T) (hV : Disjoint V T) (hb : b ∈ T)
    {α : Type*} (f : α → X) (hf : range f ⊆ T) (s₀ : α)
    (hcross : ∀ s, f s = b ↔ s = s₀) (s : α) (t : unitInterval) :
    f s = (p.trans q.symm) t ↔ s = s₀ ∧ (t : ℝ) = 1 / 2 := by
  have hmid := (path_trans_symm_mem_sides p q hp hq).2.2
  constructor
  · intro h
    have ht : (t : ℝ) = 1 / 2 :=
      (path_trans_symm_mem_trace_iff p q hp hq hU hV hb t).mp (h ▸ hf ⟨s, rfl⟩)
    have heq : t = ⟨1 / 2, by norm_num⟩ := Subtype.ext ht
    exact ⟨(hcross s).mp (by simpa only [heq, hmid] using h), ht⟩
  · rintro ⟨hs, ht⟩
    have heq : t = ⟨1 / 2, by norm_num⟩ := Subtype.ext ht
    simpa only [heq, hmid] using (hcross s).mpr hs

/-- Gluing two crossing paths gives a simple edge, also when its endpoints coincide. -/
theorem path_trans_symm_crossing {X : Type*} [TopologicalSpace X]
    {a b c : X} (p : Path a b) (q : Path c b) {U V : Set X}
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hloop : a = c → range p ∩ range q = {a, b})
    (hedge : a ≠ c → range p ∩ range q = {b})
    (hpU : ∀ t : unitInterval, t ≠ 1 → p t ∈ U)
    (hqV : ∀ t : unitInterval, t ≠ 1 → q t ∈ V) :
    InjOn (p.trans q.symm) {t : unitInterval | (t : ℝ) < 1} ∧
    (∀ t : unitInterval, (t : ℝ) < 1 / 2 → (p.trans q.symm) t ∈ U) ∧
    (∀ t : unitInterval, 1 / 2 < (t : ℝ) → (p.trans q.symm) t ∈ V) ∧
    (p.trans q.symm) ⟨1 / 2, by norm_num⟩ = b := by
  classical
  refine ⟨?_, path_trans_symm_mem_sides p q hpU hqV⟩
  by_cases h : a = c
  · subst c
    exact path_trans_symm_injOn_of_inter_eq_endpoints p q hp hq (hloop rfl)
  · have hq' : Function.Injective q.symm :=
      fun s t he => unitInterval.symm_involutive.injective (hq he)
    apply (LatticeProb.Topology.path_trans_injective hp hq' ?_).injOn
    simpa only [Path.symm_range] using hedge h

/-- Compatible terminal chart parametrizations give the standard crossing parametrization. -/
theorem path_trans_symm_chart {X : Type*} [TopologicalSpace X]
    {a b c : X} (p : Path a b) (q : Path c b) (chart : X → ℝ × ℝ)
    {r : ℝ} (hp : ∀ s : unitInterval, 1 - 2 * r < (s : ℝ) →
      chart (p s) = (1 / 2, ((s : ℝ) - 1) / 2))
    (hq : ∀ s : unitInterval, 1 - 2 * r < (s : ℝ) →
      chart (q s) = (1 / 2, (1 - (s : ℝ)) / 2)) :
    ∀ t : unitInterval, |(t : ℝ) - 1 / 2| < r →
      chart ((p.trans q.symm) t) = (1 / 2, (t : ℝ) - 1 / 2) := by
  intro t ht
  have ht' := abs_lt.mp ht
  rw [Path.trans_apply]
  split_ifs with h
  · rw [hp _ (by dsimp; linarith)]
    congr 1
    dsimp
    ring
  · change chart (q (unitInterval.symm _)) = _
    rw [hq _ (by dsimp [unitInterval.symm]; linarith)]
    congr 1
    dsimp [unitInterval.symm]
    ring

/-- Attaching an injective path to a terminal stub preserves simplicity, face
membership, and the stub's local chart parametrization. -/
theorem path_trans_terminal_chart {X : Type*} [TopologicalSpace X]
    {a b c : X} (p : Path a b) (q : Path b c) {U : Set X}
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hmeet : range p ∩ range q = {b})
    (hpU : range p ⊆ U) (hqU : ∀ s : unitInterval, s ≠ 1 → q s ∈ U)
    (chart : X → ℝ × ℝ) (k r : ℝ) (hr : r ≤ 1 / 4)
    (hchart : ∀ s : unitInterval, 1 - 4 * r < (s : ℝ) →
      chart (q s) = (1 / 2, k * (1 - (s : ℝ)) / 4)) :
    Function.Injective (p.trans q) ∧
    (∀ t : unitInterval, t ≠ 1 → (p.trans q) t ∈ U) ∧
    (∀ t : unitInterval, 1 - 2 * r < (t : ℝ) →
      chart ((p.trans q) t) = (1 / 2, k * (1 - (t : ℝ)) / 2)) := by
  refine ⟨LatticeProb.Topology.path_trans_injective hp hq hmeet, ?_, ?_⟩
  · intro t ht
    rw [Path.trans_apply]
    split_ifs with h
    · exact hpU ⟨_, rfl⟩
    · apply hqU
      intro he
      have hv := congrArg Subtype.val he
      have ht' : (t : ℝ) ≠ 1 := fun h => ht (Subtype.ext h)
      dsimp at hv
      apply ht'
      linarith
  · intro t ht
    rw [Path.trans_apply, dif_neg (not_le_of_gt (by linarith))]
    rw [hchart _ (by dsimp; linarith)]
    congr 1
    dsimp
    ring

end FiniteAvalanches.Electrical.StatementGeometry
