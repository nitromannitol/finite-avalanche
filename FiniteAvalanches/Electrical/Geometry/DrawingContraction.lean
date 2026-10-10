import FiniteAvalanches.Electrical.Geometry.ArcCollapse

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.DrawingContraction
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open scoped Classical
noncomputable section

def quotientGraph {V E W : Type} (J : CopiedGraph V E) (p : V → W) :
    CopiedGraph W {e : E // p (J.left e) ≠ p (J.right e)} :=
  ⟨fun e => p (J.left e.val), fun e => p (J.right e.val)⟩

theorem contract_edge {V E W : Type} [Fintype V] [Fintype E] [Fintype W]
    (J : CopiedGraph V E) (D : Drawing J) (e : E)
    (hne : J.left e ≠ J.right e) (p : V → W) (hp : Function.Surjective p)
    (hkernel : ∀ x y, p x = p y ↔ x = y ∨
      ((x = J.left e ∨ x = J.right e) ∧ (y = J.left e ∨ y = J.right e))) :
    ∃ q : Plane → Plane, Continuous q ∧
      (∀ x y, q x = q y ↔ x = y ∨
        (x ∈ Set.range (D.curve e) ∧ y ∈ Set.range (D.curve e))) ∧
      ∃ Q : Drawing (quotientGraph J p),
        (∀ v, Q.point (p v) = q (D.point v)) ∧
        (∀ f t, Q.curve f t = q (D.curve f.val t)) := by
  obtain ⟨q, hqcont, hq⟩ := ArcCollapse.exists_arc_collapse (D.curve e)
    (D.continuous e) (D.nonloop_curve_injective e hne)
  have point_range (v : V) : D.point v ∈ Set.range (D.curve e) ↔
      v = J.left e ∨ v = J.right e := by
    constructor
    · rintro ⟨t, ht⟩
      rcases (D.curve_vertex_iff e t v).mp ht with ⟨_, hv⟩ | ⟨_, hv⟩
      · exact Or.inl hv.symm
      · exact Or.inr hv.symm
    · rintro (rfl | rfl)
      · exact ⟨⟨0, by constructor <;> norm_num⟩, D.start e⟩
      · exact ⟨⟨1, by constructor <;> norm_num⟩, D.finish e⟩
  have points (x y : V) : q (D.point x) = q (D.point y) ↔ p x = p y := by
    rw [hq, hkernel, point_range, point_range, D.point_injective.eq_iff]
  let point (w : W) : Plane := q (D.point (Classical.choose (hp w)))
  have point_eq (v : V) : point (p v) = q (D.point v) :=
    (points _ _).mpr (Classical.choose_spec (hp (p v)))
  have point_inj : Function.Injective point := by
    intro x y h
    have he := (points (Classical.choose (hp x)) (Classical.choose (hp y))).mp h
    rwa [Classical.choose_spec (hp x), Classical.choose_spec (hp y)] at he
  have pe : p (J.left e) = p (J.right e) :=
    (hkernel _ _).mpr (Or.inr ⟨Or.inl rfl, Or.inr rfl⟩)
  have survivor_ne (f : {f : E // p (J.left f) ≠ p (J.right f)}) : f.val ≠ e := by
    intro h
    exact f.property (h.symm ▸ pe)
  have survivor_range (f : {f : E // p (J.left f) ≠ p (J.right f)})
      (t : ArcParameter) (ht : D.curve f.val t ∈ Set.range (D.curve e)) :
      t.val = 0 ∨ t.val = 1 := by
    obtain ⟨s, hs⟩ := ht
    exact (D.intersects f.val e (survivor_ne f) t s hs.symm).1
  let curve (f : {f : E // p (J.left f) ≠ p (J.right f)}) (t : ArcParameter) : Plane :=
    q (D.curve f.val t)
  have injective (f : {f : E // p (J.left f) ≠ p (J.right f)}) :
      Set.InjOn (curve f) {t | t.val < 1} := by
    intro s hs t ht h
    rcases (hq _ _).mp h with he | ⟨hsr, htr⟩
    · exact D.injective f.val hs ht he
    · have hs0 : s.val = 0 := (survivor_range f s hsr).resolve_right (ne_of_lt hs)
      have ht0 : t.val = 0 := (survivor_range f t htr).resolve_right (ne_of_lt ht)
      exact Subtype.ext (hs0.trans ht0.symm)
  have avoids (f : {f : E // p (J.left f) ≠ p (J.right f)})
      (t : ArcParameter) (ht0 : 0 < t.val) (ht1 : t.val < 1) (w : W) :
      curve f t ≠ point w := by
    intro h
    rcases (hq _ _).mp h with he | ⟨htr, _⟩
    · exact D.avoids f.val t ht0 ht1 (Classical.choose (hp w)) he
    · exact (survivor_range f t htr).elim (ne_of_gt ht0) (ne_of_lt ht1)
  have intersects (f g : {f : E // p (J.left f) ≠ p (J.right f)}) (hfg : f ≠ g)
      (s t : ArcParameter) (h : curve f s = curve g t) :
      (s.val = 0 ∨ s.val = 1) ∧ (t.val = 0 ∨ t.val = 1) := by
    rcases (hq _ _).mp h with he | ⟨hsr, htr⟩
    · exact D.intersects f.val g.val (fun hv => hfg (Subtype.ext hv)) s t he
    · exact ⟨survivor_range f s hsr, survivor_range g t htr⟩
  let Q : Drawing (quotientGraph J p) := {
    point := point
    point_injective := point_inj
    curve := curve
    continuous := fun f => hqcont.comp (D.continuous f.val)
    injective := injective
    start := fun f => (congrArg q (D.start f.val)).trans (point_eq _).symm
    finish := fun f => (congrArg q (D.finish f.val)).trans (point_eq _).symm
    avoids := avoids
    intersects := intersects }
  exact ⟨q, hqcont, hq, Q, point_eq, fun _ _ => rfl⟩

end
end FiniteAvalanches.Electrical.DrawingContraction
