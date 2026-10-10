import FiniteAvalanches.Electrical.Trees.GroveNoncrossing

/-! Circle order forces the directions and order of the actual copied tree contacts.
Circle-angle extraction from a simple boundary drawing is a separate geometric step. -/
namespace FiniteAvalanches.Electrical.StatementGeometry
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

namespace CopiedGraph
variable (J : CopiedGraph V E)

omit [Fintype V] [Fintype E] in
theorem reaches_mono {s t : Finset E} (hst : s ⊆ t) {x y : V}
    (h : J.reaches s x y) : J.reaches t x y := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail ⟨h.choose,hst h.choose_spec.1,h.choose_spec.2⟩

omit [Fintype V] [Fintype E] in
theorem reaches_insert_iff (F : Finset E) (e : E) (x y : V) :
    J.reaches (insert e F) x y ↔ J.reaches F x y ∨
      (J.reaches F x (J.left e) ∧ J.reaches F (J.right e) y) ∨
      (J.reaches F x (J.right e) ∧ J.reaches F (J.left e) y) := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl .refl
    | @tail z y _ h ih =>
      obtain ⟨f,hf,hends⟩ := h
      rcases Finset.mem_insert.mp hf with rfl | hf
      · rcases hends with hends | hends
        · rw [← hends.1] at ih
          rw [← hends.2]
          rcases ih with h | ⟨h,_⟩ | ⟨h,_⟩
          · exact Or.inr (Or.inl ⟨h,.refl⟩)
          · exact Or.inr (Or.inl ⟨h,.refl⟩)
          · exact Or.inl h
        · rw [← hends.1] at ih
          rw [← hends.2]
          rcases ih with h | ⟨h,_⟩ | ⟨h,_⟩
          · exact Or.inr (Or.inr ⟨h,.refl⟩)
          · exact Or.inl h
          · exact Or.inr (Or.inr ⟨h,.refl⟩)
      · have step : J.reaches F z y := .single ⟨f,hf,hends⟩
        exact ih.imp (fun h => h.trans step)
          (fun h => h.imp (fun h => ⟨h.1,h.2.trans step⟩) (fun h => ⟨h.1,h.2.trans step⟩))
  · intro h
    have mono {z w : V} (h : J.reaches F z w) : J.reaches (insert e F) z w :=
      J.reaches_mono (Finset.subset_insert _ _) h
    have step : J.reaches (insert e F) (J.left e) (J.right e) :=
      .single ⟨e,Finset.mem_insert_self _ _,Or.inl ⟨rfl,rfl⟩⟩
    rcases h with h | ⟨h,k⟩ | ⟨h,k⟩
    · exact mono h
    · exact ((mono h).trans step).trans (mono k)
    · exact ((mono h).trans (J.grove_reaches_symm step)).trans (mono k)

omit [Fintype V] [Fintype E] in
/-- Separation of source and ground gives exactly the two endpoint orientations. -/
theorem separating_pairings (T : J.SpanningTree) (e : E) (he : e ∈ T.val)
    (u v : V) (hsep : ¬J.reaches (T.val.erase e) u v) :
    (J.reaches (T.val.erase e) u (J.left e) ∧
      J.reaches (T.val.erase e) (J.right e) v) ∨
    (J.reaches (T.val.erase e) u (J.right e) ∧
      J.reaches (T.val.erase e) (J.left e) v) := by
  have h := T.property.2.1 u v
  rw [← Finset.insert_erase he,J.reaches_insert_iff] at h
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
    J.reaches_mono (Finset.erase_subset _ _) h
  have monoF {x y : V} (h : J.reaches F x y) : J.reaches (T.val.erase f) x y :=
    J.reaches_mono (by intro a ha; simp only [F,Finset.mem_erase] at ha ⊢; exact ⟨ha.1,ha.2.2⟩) h
  have step : J.reaches (T.val.erase e) (J.left f) (J.right f) :=
    .single ⟨f,Finset.mem_erase.mpr ⟨hef.symm,hf⟩,Or.inl ⟨rfl,rfl⟩⟩
  have hua : J.reaches F u (J.left e) := by
    rw [heq,J.reaches_insert_iff] at hu
    rcases hu with hu | ⟨h,_⟩ | ⟨h,_⟩
    · exact hu
    · exact (horder (mono h)).elim
    · exact (horder ((mono h).trans (J.grove_reaches_symm step))).elim
  have hub : J.reaches (T.val.erase f) u (J.right e) :=
    (monoF hua).tail ⟨e,Finset.mem_erase.mpr ⟨hef,he⟩,Or.inl ⟨rfl,rfl⟩⟩
  rw [heq,J.reaches_insert_iff] at hv
  rcases hv with hv | ⟨hbc,hdv⟩ | ⟨_,hcv⟩
  · exact (hsepf (hub.trans (monoF hv))).elim
  · exact ⟨hua,hbc,hdv⟩
  · exact (hsepf (hfu.trans (monoF hcv))).elim

omit [Fintype V] [Fintype E] in
/-- A simple boundary path uses distinct original copied identifiers, independently of storage orientation. -/
theorem boundary_copies_injective (m : ℕ) (p : Fin (m+1) → V)
    (hsimple : Function.Injective p) (copies : Fin m → E)
    (hends : ∀ i,
      (J.left (copies i) = p i.castSucc ∧ J.right (copies i) = p i.succ) ∨
      (J.right (copies i) = p i.castSucc ∧ J.left (copies i) = p i.succ)) :
    Function.Injective copies := by
  intro i j h
  obtain hi := hends i
  rw [h] at hi
  rcases hi with ⟨ai,bi⟩ | ⟨bi,ai⟩ <;> rcases hends j with ⟨aj,bj⟩ | ⟨bj,aj⟩
  · exact Fin.castSucc_injective m (hsimple (ai.symm.trans aj))
  · have ha := congrArg Fin.val (hsimple (ai.symm.trans aj))
    have hb := congrArg Fin.val (hsimple (bi.symm.trans bj))
    simp only [Fin.val_castSucc,Fin.val_succ] at ha hb
    omega
  · have ha := congrArg Fin.val (hsimple (bi.symm.trans bj))
    have hb := congrArg Fin.val (hsimple (ai.symm.trans aj))
    simp only [Fin.val_castSucc,Fin.val_succ] at ha hb
    omega
  · exact Fin.castSucc_injective m (hsimple (bi.symm.trans bj))

end CopiedGraph

namespace Drawing
variable {J : CopiedGraph V E} (D : Drawing J)

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
    have h := J.separating_pairings T e he (p 0) (p (Fin.last m)) hhit
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
    exact (D.grove_alternating_walks_impossible
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
  have hv := (D.boundary_copy_forward T hvertices hedges m p θ hθ hspan hpoint i e hei he hhit).2
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
  exact D.grove_alternating_walks_impossible
    (T.val.erase e) (p 0) (p j.succ) (p i.succ) (p (Fin.last m))
    huf hv hn hvertices hedges
    (θ 0) (θ i.succ) (θ j.succ) (θ (Fin.last m))
    (hθ h0i) (hθ hij') (hθ hjm') hspan
    (hpoint 0) (hpoint j.succ) (hpoint i.succ) (hpoint (Fin.last m))

end Drawing
end
end FiniteAvalanches.Electrical.StatementGeometry
