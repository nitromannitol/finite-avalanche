import FiniteAvalanches.Electrical.Geometry.SimpleChain

namespace FiniteAvalanches.Electrical.StatementGeometry
open Set unitInterval
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

namespace Drawing

/-- Either storage direction gives an actual forward arc, with no fabricated curve. -/
theorem oriented_arc (D : Drawing J) (a b : V) (hab : a ≠ b) (e : E)
    (hends : (J.left e = a ∧ J.right e = b) ∨
      (J.right e = a ∧ J.left e = b)) :
    ∃ f : Path (D.point a) (D.point b), Function.Injective f ∧
      (∀ t, ∃ s, f t = D.curve e s) ∧
      (∀ t v, f t = D.point v → t = 0 ∨ t = 1) := by
  have hne : J.left e ≠ J.right e := by
    rcases hends with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · simpa [ha, hb] using hab
    · simpa [ha, hb] using hab.symm
  let raw : Path (D.point (J.left e)) (D.point (J.right e)) :=
    ⟨⟨D.curve e, D.continuous e⟩, D.start e, D.finish e⟩
  have hi : Function.Injective raw := D.nonloop_curve_injective e hne
  rcases hends with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · let f := raw.cast (congrArg D.point ha.symm) (congrArg D.point hb.symm)
    refine ⟨f, hi, fun t => ⟨t, rfl⟩, ?_⟩
    intro t v h
    rcases (D.curve_vertex_iff e t v).mp h with ⟨ht, _⟩ | ⟨ht, _⟩
    · exact Or.inl (Subtype.ext ht)
    · exact Or.inr (Subtype.ext ht)
  · let f := raw.symm.cast (congrArg D.point ha.symm) (congrArg D.point hb.symm)
    have hf : Function.Injective f := hi.comp (fun s t h =>
      unitInterval.symm_bijective.injective h)
    refine ⟨f, hf, fun t => ⟨unitInterval.symm t, rfl⟩, ?_⟩
    intro t v h
    rcases (D.curve_vertex_iff e (unitInterval.symm t) v).mp h with ⟨ht, _⟩ | ⟨ht, _⟩
    · exact Or.inr (Subtype.ext (by change (t : ℝ) = 1; change 1 - (t : ℝ) = 0 at ht; linarith))
    · exact Or.inl (Subtype.ext (by change (t : ℝ) = 0; change 1 - (t : ℝ) = 1 at ht; linarith))

/-- The IDs of a simple boundary path remain distinct even with reversed parallel copies. -/
theorem simple_path_copies_injective (_D : Drawing J) (m : ℕ) (p : Fin (m + 1) → V)
    (hp : Function.Injective p) (copies : Fin m → E)
    (hends : ∀ i, (J.left (copies i) = p i.castSucc ∧ J.right (copies i) = p i.succ) ∨
      (J.right (copies i) = p i.castSucc ∧ J.left (copies i) = p i.succ)) :
    Function.Injective copies := by
  intro i j h
  have hi := hends i
  rw [h] at hi
  rcases hi with ⟨ai, bi⟩ | ⟨bi, ai⟩ <;> rcases hends j with ⟨aj, bj⟩ | ⟨bj, aj⟩
  · exact Fin.castSucc_injective m (hp (ai.symm.trans aj))
  · have ha := congrArg Fin.val (hp (ai.symm.trans aj))
    have hb := congrArg Fin.val (hp (bi.symm.trans bj))
    simp only [Fin.val_castSucc, Fin.val_succ] at ha hb
    omega
  · have ha := congrArg Fin.val (hp (bi.symm.trans bj))
    have hb := congrArg Fin.val (hp (ai.symm.trans aj))
    simp only [Fin.val_castSucc, Fin.val_succ] at ha hb
    omega
  · exact Fin.castSucc_injective m (hp (bi.symm.trans bj))

/-- A nonempty simple boundary path is realized by its actual original curves, in path order. -/
theorem boundary_path_realization (D : Drawing J) (n : ℕ) (p : Fin (n + 2) → V)
    (hp : Function.Injective p) (copies : Fin (n + 1) → E)
    (hends : ∀ i, (J.left (copies i) = p i.castSucc ∧ J.right (copies i) = p i.succ) ∨
      (J.right (copies i) = p i.castSucc ∧ J.left (copies i) = p i.succ)) :
    ∃ f : Path (D.point (p 0)) (D.point (p (Fin.last (n + 1)))),
      Function.Injective f ∧ ∃ τ : Fin (n + 2) → I,
      StrictMono τ ∧ τ 0 = 0 ∧ τ (Fin.last (n + 1)) = 1 ∧
      (∀ k, f (τ k) = D.point (p k)) ∧
      (∀ t, ∃ i s, f t = D.curve (copies i) s) := by
  have hex (i : Fin (n + 1)) := D.oriented_arc (p i.castSucc) (p i.succ)
    (hp.ne (by intro h; have := congrArg Fin.val h; simp at this)) (copies i) (hends i)
  choose arcs hi hr hv using hex
  have hc : Function.Injective copies := D.simple_path_copies_injective _ _ hp _ hends
  have hcross : ∀ i j, i ≠ j → ∀ s t, arcs i s = arcs j t →
      (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1) := by
    intro i j hij s t h
    obtain ⟨s', hs⟩ := hr i s
    obtain ⟨t', ht⟩ := hr j t
    have he := D.intersects _ _ (hc.ne hij) s' t' (hs.symm.trans (h.trans ht))
    have hit (i : Fin (n + 1)) (q : I) (r : ArcParameter)
        (hq : arcs i q = D.curve (copies i) r) (he : r.val = 0 ∨ r.val = 1) : q = 0 ∨ q = 1 := by
      rcases he with he | he
      · have hr0 : r = ⟨0, by constructor <;> norm_num⟩ := Subtype.ext he
        apply hv i q (J.left (copies i))
        rw [hq, hr0, D.start]
      · have hr1 : r = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext he
        apply hv i q (J.right (copies i))
        rw [hq, hr1, D.finish]
    exact ⟨hit i s s' hs he.1, hit j t t' ht he.2⟩
  obtain ⟨f, hf, τ, hτ, h0, h1, hvisit, hrange⟩ :=
    simple_chain_realization n (fun k => D.point (p k)) (D.point_injective.comp hp) arcs hi hcross
  refine ⟨f, hf, τ, hτ, h0, h1, hvisit, ?_⟩
  intro t
  obtain ⟨i, s, hs⟩ := hrange t
  obtain ⟨r, hr⟩ := hr i s
  exact ⟨i, r, hs.trans hr⟩

end Drawing
end
end FiniteAvalanches.Electrical.StatementGeometry
