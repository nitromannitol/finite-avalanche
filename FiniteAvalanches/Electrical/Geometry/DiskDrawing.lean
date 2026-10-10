import FiniteAvalanches.Trees.PathCopies
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Connected.Basic
import FiniteAvalanches.Electrical.Green.Grounded

/-! Literal geometric disk drawings and exact boundary-path statement types.
No probabilistic or electrical conclusion is included in the drawing data. -/

namespace FiniteAvalanches.Electrical.StatementGeometry
open scoped Classical BigOperators
open Trees


/-- A copied graph retains every original ID, including self-loops. -/
structure CopiedGraph (V E : Type) where
  left : E → V
  right : E → V

namespace CopiedGraph
variable {V E : Type} [Fintype V] [Fintype E]

/-- Literal finite copied-walk reachability, including length-zero walks. -/
def reaches (J : CopiedGraph V E) (T : Finset E) : V → V → Prop :=
  Relation.ReflTransGen (fun x y => ∃ e ∈ T,
    (J.left e = x ∧ J.right e = y) ∨ (J.right e = x ∧ J.left e = y))

/-- Ordinary trees on the full original vertex set and original copied IDs. -/
abbrev SpanningTree (J : CopiedGraph V E) := {T : Finset E //
  (Set.univ : Set V).Nonempty ∧ (∀ x y, J.reaches T x y) ∧
    ∀ e ∈ T, ¬J.reaches (T.erase e) (J.left e) (J.right e)}

/-- The literal separation characterization of original-copy membership on the tree path. -/
noncomputable def pathIndicator (J : CopiedGraph V E) (T : J.SpanningTree)
    (u v : V) (e : E) : ℝ :=
  if e ∈ T.val ∧ ¬J.reaches (T.val.erase e) u v then 1 else 0

omit [Fintype V] [Fintype E] in
/-- An original loop remains a network copy and is excluded by the actual tree predicate. -/
theorem loop_not_mem (J : CopiedGraph V E) (T : J.SpanningTree)
    (e : E) (hloop : J.left e = J.right e) : e ∉ T.val := by
  intro he
  apply T.property.2.2 e he
  rw [hloop]
  exact Relation.ReflTransGen.refl

end CopiedGraph

abbrev ArcParameter := Set.Icc (0 : ℝ) 1

/-- An actual plane drawing of the copied graph by simple continuous arcs. -/
structure Drawing {V E : Type} [Fintype V] [Fintype E] (G : CopiedGraph V E) where
  point : V → ℝ × ℝ
  point_injective : Function.Injective point
  curve : E → ArcParameter → ℝ × ℝ
  continuous : ∀ e, Continuous (curve e)
  injective : ∀ e, Set.InjOn (curve e) {t | t.val < 1}
  start : ∀ e, curve e ⟨0,by constructor <;> norm_num⟩ = point (G.left e)
  finish : ∀ e, curve e ⟨1,by constructor <;> norm_num⟩ = point (G.right e)
  avoids : ∀ e t, 0 < t.val → t.val < 1 → ∀ v, curve e t ≠ point v
  intersects : ∀ e f, e ≠ f → ∀ s t, curve e s = curve f t →
    (s.val = 0 ∨ s.val = 1) ∧ (t.val = 0 ∨ t.val = 1)

/-- The Euclidean closed unit disk, in the literal two real coordinates. -/
def disk : Set (ℝ × ℝ) := {z | z.1^2 + z.2^2 ≤ 1}
def circle : Set (ℝ × ℝ) := {z | z.1^2 + z.2^2 = 1}

namespace Drawing
variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E} (drawing : Drawing J)

/-- An edge curve hits an original vertex exactly at one of its prescribed endpoints. -/
theorem curve_vertex_iff (e : E) (t : ArcParameter) (v : V) :
    drawing.curve e t = drawing.point v ↔
    (t.val = 0 ∧ J.left e = v) ∨ (t.val = 1 ∧ J.right e = v) := by
  constructor
  · intro h
    by_cases ht0 : t.val = 0
    · have he : t = ⟨0, by constructor <;> norm_num⟩ := Subtype.ext ht0
      rw [he, drawing.start] at h
      exact Or.inl ⟨ht0, drawing.point_injective h⟩
    by_cases ht1 : t.val = 1
    · have he : t = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext ht1
      rw [he, drawing.finish] at h
      exact Or.inr ⟨ht1, drawing.point_injective h⟩
    · exact (drawing.avoids e t (lt_of_le_of_ne t.property.1 (Ne.symm ht0))
        (lt_of_le_of_ne t.property.2 ht1) v h).elim
  · rintro (⟨ht, hv⟩ | ⟨ht, hv⟩)
    · have he : t = ⟨0, by constructor <;> norm_num⟩ := Subtype.ext ht
      rw [he, drawing.start, hv]
    · have he : t = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext ht
      rw [he, drawing.finish, hv]

/-- Restricting to a nonloop edge turns the literal half-open simplicity into full simplicity. -/
theorem nonloop_curve_injective (e : E) (hne : J.left e ≠ J.right e) :
    Function.Injective (drawing.curve e) := by
  intro s t h
  by_cases hs : s.val = 1
  · have he : s = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext hs
    have hv : drawing.curve e t = drawing.point (J.right e) := by
      rw [← h, he, drawing.finish]
    rcases (drawing.curve_vertex_iff e t _).mp hv with ⟨ht, hn⟩ | ⟨ht, _⟩
    · exact (hne hn).elim
    · exact Subtype.ext (hs.trans ht.symm)
  by_cases ht : t.val = 1
  · have he : t = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext ht
    have hv : drawing.curve e s = drawing.point (J.right e) := by
      rw [h, he, drawing.finish]
    rcases (drawing.curve_vertex_iff e s _).mp hv with ⟨_, hn⟩ | ⟨hs', _⟩
    · exact (hne hn).elim
    · exact (hs hs').elim
  · exact drawing.injective e (lt_of_le_of_ne s.property.2 hs)
      (lt_of_le_of_ne t.property.2 ht) h

/-- The literal geometric realization of a vertex set and its original copied edges. -/
def trace (C : Set V) (s : Finset E) : Set (ℝ × ℝ) :=
  (drawing.point '' C) ∪ {z | ∃ e ∈ s, ∃ t, drawing.curve e t = z}

/-- Copied edges supported on C can hit only vertices in C. -/
theorem curve_vertex_mem {C : Set V} {s : Finset E}
    (hs : ∀ e ∈ s, J.left e ∈ C ∧ J.right e ∈ C)
    (e : E) (he : e ∈ s) (t : ArcParameter) (v : V)
    (h : drawing.curve e t = drawing.point v) : v ∈ C := by
  rcases (drawing.curve_vertex_iff e t v).mp h with ⟨_, hv⟩ | ⟨_, hv⟩
  · exact hv ▸ (hs e he).1
  · exact hv ▸ (hs e he).2

/-- Distinct forest components have literally disjoint drawings, even with loops and parallels.
This supplies geometric disjointness to a Jordan argument; no no-crossing conclusion is assumed. -/
theorem traces_disjoint {C D : Set V} {s t : Finset E} (hCD : Disjoint C D)
    (hs : ∀ e ∈ s, J.left e ∈ C ∧ J.right e ∈ C)
    (ht : ∀ e ∈ t, J.left e ∈ D ∧ J.right e ∈ D) :
    Disjoint (drawing.trace C s) (drawing.trace D t) := by
  apply Set.disjoint_left.mpr
  intro z hzC hzD
  rcases hzC with ⟨x, hx, rfl⟩ | ⟨e, he, q, hq⟩
  · rcases hzD with ⟨y, hy, hyx⟩ | ⟨f, hf, r, hr⟩
    · have hyx' := drawing.point_injective hyx
      exact Set.disjoint_left.mp hCD hx (hyx' ▸ hy)
    · exact Set.disjoint_left.mp hCD hx (drawing.curve_vertex_mem ht f hf r x hr)
  · rcases hzD with ⟨y, hy, hyz⟩ | ⟨f, hf, r, hr⟩
    · have hyC : y ∈ C := drawing.curve_vertex_mem hs e he q y (hq.trans hyz.symm)
      exact Set.disjoint_left.mp hCD hyC hy
    · by_cases hef : e = f
      · subst f
        exact Set.disjoint_left.mp hCD (hs e he).1 (ht e hf).1
      · have hqr := drawing.intersects e f hef q r (hq.trans hr.symm)
        rcases hqr.2 with hr0 | hr1
        · have hr' : r = ⟨0, by constructor <;> norm_num⟩ := Subtype.ext hr0
          have hv : drawing.curve e q = drawing.point (J.left f) := by
            rw [hq, ← hr, hr', drawing.start]
          exact Set.disjoint_left.mp hCD (drawing.curve_vertex_mem hs e he q _ hv) (ht f hf).1
        · have hr' : r = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext hr1
          have hv : drawing.curve e q = drawing.point (J.right f) := by
            rw [hq, ← hr, hr', drawing.finish]
          exact Set.disjoint_left.mp hCD (drawing.curve_vertex_mem hs e he q _ hv) (ht f hf).2

/-- A real finite copied walk supplies a compact connected geometric set in its component trace. -/
theorem reachable_continuum {C : Set V} {s : Finset E}
    (_hs : ∀ e ∈ s, J.left e ∈ C ∧ J.right e ∈ C)
    (x : V) (hx : x ∈ C) (y : V) (hxy : J.reaches s x y) :
    ∃ K : Set (ℝ × ℝ), IsCompact K ∧ IsConnected K ∧ K ⊆ drawing.trace C s ∧
      drawing.point x ∈ K ∧ drawing.point y ∈ K := by
  induction hxy with
  | refl =>
    refine ⟨{drawing.point x}, isCompact_singleton, isConnected_singleton, ?_, by simp, by simp⟩
    intro z hz
    have hz' : z = drawing.point x := Set.mem_singleton_iff.mp hz
    subst z
    exact Or.inl ⟨x, hx, rfl⟩
  | @tail y z h hyz ih =>
    obtain ⟨K, hKc, hKconn, hKt, hxK, hyK⟩ := ih
    obtain ⟨e, he, heyz⟩ := hyz
    let A := Set.range (drawing.curve e)
    have hyA : drawing.point y ∈ A := by
      rcases heyz with h | h
      · exact ⟨⟨0, by constructor <;> norm_num⟩, by rw [drawing.start, h.1]⟩
      · exact ⟨⟨1, by constructor <;> norm_num⟩, by rw [drawing.finish, h.1]⟩
    have hzA : drawing.point z ∈ A := by
      rcases heyz with h | h
      · exact ⟨⟨1, by constructor <;> norm_num⟩, by rw [drawing.finish, h.2]⟩
      · exact ⟨⟨0, by constructor <;> norm_num⟩, by rw [drawing.start, h.2]⟩
    refine ⟨K ∪ A, hKc.union (isCompact_range (drawing.continuous e)),
      hKconn.union ⟨drawing.point y, hyK, hyA⟩ (isConnected_range (drawing.continuous e)),
      ?_, Or.inl hxK, Or.inr hzA⟩
    intro w hw
    rcases hw with hw | ⟨t, ht⟩
    · exact hKt hw
    · exact Or.inr ⟨e, he, t, ht⟩

/-- Two disjoint forest components give disjoint actual continua joining their terminals. -/
theorem disjoint_connecting_continua {C D : Set V} {s t : Finset E}
    (hCD : Disjoint C D)
    (hs : ∀ e ∈ s, J.left e ∈ C ∧ J.right e ∈ C)
    (ht : ∀ e ∈ t, J.left e ∈ D ∧ J.right e ∈ D)
    (x₀ x₁ y₀ y₁ : V) (hx : x₀ ∈ C) (hy : y₀ ∈ D)
    (hxx : J.reaches s x₀ x₁) (hyy : J.reaches t y₀ y₁)
    (hvertices : ∀ x, drawing.point x ∈ disk)
    (hedges : ∀ e q, drawing.curve e q ∈ disk) :
    ∃ K L : Set (ℝ × ℝ), IsCompact K ∧ IsConnected K ∧ IsCompact L ∧ IsConnected L ∧
      K ⊆ disk ∧ L ⊆ disk ∧ Disjoint K L ∧
      drawing.point x₀ ∈ K ∧ drawing.point x₁ ∈ K ∧
      drawing.point y₀ ∈ L ∧ drawing.point y₁ ∈ L := by
  obtain ⟨K, hKc, hKconn, hKt, hx₀, hx₁⟩ := drawing.reachable_continuum hs x₀ hx x₁ hxx
  obtain ⟨L, hLc, hLconn, hLt, hy₀, hy₁⟩ := drawing.reachable_continuum ht y₀ hy y₁ hyy
  have htrace (A : Set V) (F : Finset E) : drawing.trace A F ⊆ disk := by
    intro z hz
    rcases hz with ⟨v, _, rfl⟩ | ⟨e, _, q, hq⟩
    · exact hvertices v
    · exact hq ▸ hedges e q
  exact ⟨K, L, hKc, hKconn, hLc, hLconn, hKt.trans (htrace C s),
    hLt.trans (htrace D t), (drawing.traces_disjoint hCD hs ht).mono hKt hLt,
    hx₀, hx₁, hy₀, hy₁⟩

end Drawing
end FiniteAvalanches.Electrical.StatementGeometry
