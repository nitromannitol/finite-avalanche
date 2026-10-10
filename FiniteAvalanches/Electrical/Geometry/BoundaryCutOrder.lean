import FiniteAvalanches.Electrical.Trees.TwoCopyGroves
import FiniteAvalanches.Electrical.Geometry.DiskCrossing

/-! Circle order determines actual copied-tree cut direction and order. -/
namespace FiniteAvalanches.Electrical.StatementGeometry
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]
namespace CopiedGraph.TwoCopy
variable (J : CopiedGraph V E)
/-- The actual component of a vertex in an original-copy edge subset. -/
def component (F : Finset E) (root : V) : Set V :=
  {x | J.reaches F root x}

/-- Keep the original IDs in the component, including their multiplicities. -/
def componentCopies (F : Finset E) (root : V) : Finset E :=
  F.filter (fun e => J.left e ∈ component J F root)

omit [Fintype V] [Fintype E] in
/-- Component restriction retains both actual endpoints of every selected copy. -/
theorem component_copies_supported (F : Finset E) (root : V) :
    ∀ e ∈ componentCopies J F root,
      J.left e ∈ component J F root ∧ J.right e ∈ component J F root := by
  intro e he
  obtain ⟨hes, hl⟩ := Finset.mem_filter.mp he
  exact ⟨hl, hl.tail ⟨e,hes,Or.inl ⟨rfl,rfl⟩⟩⟩

omit [Fintype V] [Fintype E] in
/-- The restriction retains every literal walk from its root. -/
theorem reaches_component_copies {F : Finset E} {root y : V}
    (h : J.reaches F root y) : J.reaches (componentCopies J F root) root y := by
  induction h with
  | refl => exact .refl
  | @tail y z h hyz ih =>
    obtain ⟨e, he, hends⟩ := hyz
    have hl : J.left e ∈ component J F root := by
      rcases hends with hends | hends
      · exact hends.1 ▸ h
      · exact h.tail ⟨e,he,Or.inr ⟨hends.1,rfl⟩⟩
    exact ih.tail ⟨e,Finset.mem_filter.mpr ⟨he,hl⟩,hends⟩

omit [Fintype V] [Fintype E] in
/-- Component disjointness comes from the actual copied reachability relation. -/
theorem components_disjoint {F : Finset E} {x y : V}
    (hxy : ¬J.reaches F x y) :
    Disjoint (component J F x) (component J F y) := by
  apply Set.disjoint_left.mpr
  intro z hxz hyz
  exact hxy (hxz.trans (reaches_symm J hyz))
omit [Fintype V] [Fintype E] in
/-- Separation of source and ground gives exactly the two endpoint orientations. -/
theorem separating_pairings (T : J.SpanningTree) (e : E) (he : e ∈ T.val)
    (u v : V) (hsep : ¬J.reaches (T.val.erase e) u v) :
    (J.reaches (T.val.erase e) u (J.left e) ∧
      J.reaches (T.val.erase e) (J.right e) v) ∨
    (J.reaches (T.val.erase e) u (J.right e) ∧
      J.reaches (T.val.erase e) (J.left e) v) := by
  have h := T.property.2.1 u v
  rw [← Finset.insert_erase he,reaches_insert_iff J] at h
  exact h.resolve_left hsep

omit [Fintype V] [Fintype E] in
/-- The three literal connections remaining after both original copies are erased. -/
theorem two_erased_pairings_of_cuts (T : J.SpanningTree) (u v : V) (e f : E)
    (hef : e ≠ f) (he : e ∈ T.val) (hf : f ∈ T.val)
    (hu : J.reaches (T.val.erase e) u (J.left e))
    (hv : J.reaches (T.val.erase e) (J.right e) v)
    (hfu : J.reaches (T.val.erase f) u (J.left f))
    (hsepf : ¬J.reaches (T.val.erase f) u v)
    (horder : ¬J.reaches (T.val.erase e) u (J.left f)) :
    J.reaches ((T.val.erase e).erase f) u (J.left e) ∧
    J.reaches ((T.val.erase e).erase f) (J.right e) (J.left f) ∧
    J.reaches ((T.val.erase e).erase f) (J.right f) v := by
  let F := (T.val.erase e).erase f
  have heq : T.val.erase e = insert f F :=
    (Finset.insert_erase (Finset.mem_erase.mpr ⟨hef.symm,hf⟩)).symm
  have mono {x y : V} (h : J.reaches F x y) : J.reaches (T.val.erase e) x y :=
    reaches_mono J (Finset.erase_subset _ _) h
  have monoF {x y : V} (h : J.reaches F x y) : J.reaches (T.val.erase f) x y :=
    reaches_mono J (by intro a ha; simp only [F,Finset.mem_erase] at ha ⊢; exact ⟨ha.1,ha.2.2⟩) h
  have step : J.reaches (T.val.erase e) (J.left f) (J.right f) :=
    .single ⟨f,Finset.mem_erase.mpr ⟨hef.symm,hf⟩,Or.inl ⟨rfl,rfl⟩⟩
  have hua : J.reaches F u (J.left e) := by
    rw [heq,reaches_insert_iff J] at hu
    rcases hu with hu | ⟨h,_⟩ | ⟨h,_⟩
    · exact hu
    · exact (horder (mono h)).elim
    · exact (horder ((mono h).trans (reaches_symm J step))).elim
  have hub : J.reaches (T.val.erase f) u (J.right e) :=
    (monoF hua).tail ⟨e,Finset.mem_erase.mpr ⟨hef,he⟩,Or.inl ⟨rfl,rfl⟩⟩
  rw [heq,reaches_insert_iff J] at hv
  rcases hv with hv | ⟨hbc,hdv⟩ | ⟨_,hcv⟩
  · exact (hsepf (hub.trans (monoF hv))).elim
  · exact ⟨hua,hbc,hdv⟩
  · exact (hsepf (hfu.trans (monoF hcv))).elim

end CopiedGraph.TwoCopy
namespace Drawing.TwoCopy
open CopiedGraph.TwoCopy
variable {J : CopiedGraph V E} (D : Drawing J)
/-- Two separated actual copied components cannot join alternating disk terminals. -/
theorem alternating_components_impossible
    (F : Finset E) (a b c d : V)
    (hab : J.reaches F a b) (hcd : J.reaches F c d) (hac : ¬J.reaches F a c)
    (hvertices : ∀ x, D.point x ∈ disk)
    (hedges : ∀ e q, D.curve e q ∈ disk)
    (θ₀ θ₁ θ₂ θ₃ : ℝ)
    (h₀₁ : θ₀ < θ₁) (h₁₂ : θ₁ < θ₂) (h₂₃ : θ₂ < θ₃)
    (h₃₀ : θ₃ < θ₀ + 2 * Real.pi)
    (pa : D.point a = (Real.cos θ₀,Real.sin θ₀))
    (pb : D.point b = (Real.cos θ₂,Real.sin θ₂))
    (pc : D.point c = (Real.cos θ₁,Real.sin θ₁))
    (pd : D.point d = (Real.cos θ₃,Real.sin θ₃)) : False := by
  exact D.alternating_walks_impossible (components_disjoint J hac)
    (component_copies_supported J F a) (component_copies_supported J F c)
    a b c d Relation.ReflTransGen.refl Relation.ReflTransGen.refl
    (reaches_component_copies J hab) (reaches_component_copies J hcd)
    hvertices hedges θ₀ θ₁ θ₂ θ₃ h₀₁ h₁₂ h₂₃ h₃₀ pa pb pc pd

/-- A source-ground tree path cannot use a boundary copy backwards.
The original storage orientation may be either direction. Endpoint coincidences are included. -/
theorem boundary_copy_forward (T : J.SpanningTree)
    (hvertices : ∀ x, D.point x ∈ disk) (hedges : ∀ e t, D.curve e t ∈ disk)
    (m : ℕ) (p : Fin (m+1) → V) (θ : Fin (m+1) → ℝ)
    (hθ : StrictMono θ) (hspan : θ (Fin.last m) < θ 0 + 2 * Real.pi)
    (hpoint : ∀ k, D.point (p k) = (Real.cos (θ k),Real.sin (θ k)))
    (k : Fin m) (e : E)
    (hends : (J.left e = p k.castSucc ∧ J.right e = p k.succ) ∨
      (J.right e = p k.castSucc ∧ J.left e = p k.succ))
    (he : e ∈ T.val) (hhit : ¬J.reaches (T.val.erase e) (p 0) (p (Fin.last m))) :
    J.reaches (T.val.erase e) (p 0) (p k.castSucc) ∧
      J.reaches (T.val.erase e) (p k.succ) (p (Fin.last m)) := by
  have hp : (J.reaches (T.val.erase e) (p 0) (p k.castSucc) ∧
      J.reaches (T.val.erase e) (p k.succ) (p (Fin.last m))) ∨
      (J.reaches (T.val.erase e) (p 0) (p k.succ) ∧
      J.reaches (T.val.erase e) (p k.castSucc) (p (Fin.last m))) := by
    have h := separating_pairings J T e he (p 0) (p (Fin.last m)) hhit
    rcases hends with ⟨ha,hb⟩ | ⟨hb,ha⟩
    · simpa only [ha,hb] using h
    · simpa only [ha,hb,or_comm] using h
  rcases hp with hp | ⟨hub,hav⟩
  · exact hp
  · by_cases hk0 : k.val = 0
    · have hk : k.castSucc = (0 : Fin (m+1)) := Fin.ext hk0
      rw [hk] at hav
      exact (hhit hav).elim
    by_cases hkm : k.succ = Fin.last m
    · rw [hkm] at hub
      exact (hhit hub).elim
    have h0k : (0 : Fin (m+1)) < k.castSucc := by change 0 < k.val; omega
    have hkl : k.castSucc < k.succ := by change k.val < k.val+1; omega
    have hlm : k.succ < Fin.last m := by
      have hn : k.val+1 ≠ m := fun h => hkm (Fin.ext h)
      change k.val+1 < m
      omega
    have hnot : ¬J.reaches (T.val.erase e) (p 0) (p k.castSucc) :=
      fun h => hhit (h.trans hav)
    exact (alternating_components_impossible D
      (T.val.erase e) (p 0) (p k.succ) (p k.castSucc) (p (Fin.last m))
      hub hav hnot hvertices hedges
      (θ 0) (θ k.castSucc) (θ k.succ) (θ (Fin.last m))
      (hθ h0k) (hθ hkl) (hθ hlm) hspan
      (hpoint 0) (hpoint k.succ) (hpoint k.castSucc) (hpoint (Fin.last m))).elim

/-- A later boundary copy lies beyond an earlier used copy's source component. -/
theorem boundary_copies_increasing (T : J.SpanningTree)
    (hvertices : ∀ x, D.point x ∈ disk) (hedges : ∀ e t, D.curve e t ∈ disk)
    (m : ℕ) (p : Fin (m+1) → V) (θ : Fin (m+1) → ℝ)
    (hθ : StrictMono θ) (hspan : θ (Fin.last m) < θ 0 + 2 * Real.pi)
    (hpoint : ∀ k, D.point (p k) = (Real.cos (θ k),Real.sin (θ k)))
    (i j : Fin m) (hij : i < j) (e f : E) (hef : e ≠ f)
    (hei : (J.left e = p i.castSucc ∧ J.right e = p i.succ) ∨
      (J.right e = p i.castSucc ∧ J.left e = p i.succ))
    (hfj : (J.left f = p j.castSucc ∧ J.right f = p j.succ) ∨
      (J.right f = p j.castSucc ∧ J.left f = p j.succ))
    (he : e ∈ T.val) (hf : f ∈ T.val)
    (hhit : ¬J.reaches (T.val.erase e) (p 0) (p (Fin.last m))) :
    ¬J.reaches (T.val.erase e) (p 0) (p j.castSucc) := by
  intro h
  have hv := (boundary_copy_forward D T hvertices hedges m p θ hθ hspan hpoint i e hei he hhit).2
  have step : J.reaches (T.val.erase e) (p j.castSucc) (p j.succ) := by
    apply Relation.ReflTransGen.single
    refine ⟨f,Finset.mem_erase.mpr ⟨hef.symm,hf⟩,?_⟩
    rcases hfj with ⟨ha,hb⟩ | ⟨hb,ha⟩
    · exact Or.inl ⟨ha,hb⟩
    · exact Or.inr ⟨hb,ha⟩
  have huf := h.trans step
  by_cases hjm : j.succ = Fin.last m
  · rw [hjm] at huf
    exact hhit huf
  have h0i : (0 : Fin (m+1)) < i.succ := by change 0 < i.val+1; omega
  have hij' : i.succ < j.succ := by change i.val+1 < j.val+1; exact Nat.add_lt_add_right hij 1
  have hjm' : j.succ < Fin.last m := by
    have hn : j.val+1 ≠ m := fun h => hjm (Fin.ext h)
    change j.val+1 < m
    omega
  have hn : ¬J.reaches (T.val.erase e) (p 0) (p i.succ) := fun h => hhit (h.trans hv)
  exact alternating_components_impossible D
    (T.val.erase e) (p 0) (p j.succ) (p i.succ) (p (Fin.last m))
    huf hv hn hvertices hedges
    (θ 0) (θ i.succ) (θ j.succ) (θ (Fin.last m))
    (hθ h0i) (hθ hij') (hθ hjm') hspan
    (hpoint 0) (hpoint j.succ) (hpoint i.succ) (hpoint (Fin.last m))

end Drawing.TwoCopy
end
end FiniteAvalanches.Electrical.StatementGeometry
