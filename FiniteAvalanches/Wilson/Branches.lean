import FiniteAvalanches.Wilson.CopiedWalk

/-! Adding a simple copied branch at its unique old-root contact preserves an
actual component tree. Acyclicity uses individual copies, including parallel ones. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.CopiedNetwork
open Quiver FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)

theorem is_forest_insert_leaf {F : Finset E} (hF : G.is_forest F) (e : E) (v : V)
    (hev : G.left e = v ∨ G.right e = v)
    (hv : ∀ f ∈ F, G.left f ≠ v ∧ G.right f ≠ v) : G.is_forest (insert e F) := by
  have hnot : e ∉ F := by
    intro he
    rcases hev with h | h
    · exact (hv e he).1 h
    · exact (hv e he).2 h
  let φ : V → V := fun x => if x = v then other G v ⟨e, hev⟩ else x
  have hfix (f : E) (hf : f ∈ F) : φ (G.left f) = G.left f ∧ φ (G.right f) = G.right f := by
    simp only [φ, if_neg (hv f hf).1, if_neg (hv f hf).2, and_self]
  have hcollapse : φ (G.left e) = φ (G.right e) := by
    rcases hev with hl | hr
    · have hn : G.right e ≠ v := fun h => G.loopless e (hl.trans h.symm)
      simp [φ, hl, other]
    · have hn : G.left e ≠ v := fun h => G.loopless e (h.trans hr.symm)
      simp [φ, hr, hn, other]
  intro f hf hreach
  by_cases hfe : f = e
  · subst f
    have hr : G.reaches F (G.left e) (G.right e) := by
      simpa [Finset.erase_insert, hnot] using hreach
    have hs : G.supported ({v}ᶜ) F := fun f hf => ⟨(hv f hf).1, (hv f hf).2⟩
    have hm : G.left e ≠ v ↔ G.right e ≠ v :=
      G.reaches_mem_iff (fun f hf => iff_of_true (hs f hf).1 (hs f hf).2) hr
    rcases hev with hl | hr
    · exact (hm.mpr (fun h => G.loopless e (hl.trans h.symm))) hl
    · exact (hm.mp (fun h => G.loopless e (h.trans hr.symm))) hr
  · have hfF : f ∈ F := (Finset.mem_insert.mp hf).resolve_left hfe
    apply hF f hfF
    have hm : G.reaches (F.erase f) (φ (G.left f)) (φ (G.right f)) := by
      apply Relation.ReflTransGen.lift' φ (fun x y h => ?_) _ _ hreach
      dsimp only [Function.onFun]
      obtain ⟨a, ha, hxy⟩ := h
      have haf := (Finset.mem_erase.mp ha).1
      rcases Finset.mem_insert.mp (Finset.mem_erase.mp ha).2 with hae | haF
      · subst a
        rcases hxy with h | h
        · rw [← h.1, ← h.2, hcollapse]
        · rw [← h.1, ← h.2, hcollapse]
      · rcases hxy with h | h
        · rw [← h.1, ← h.2, (hfix a haF).1, (hfix a haF).2]
          exact Relation.ReflTransGen.single ⟨a, Finset.mem_erase.mpr ⟨haf, haF⟩, Or.inl ⟨rfl, rfl⟩⟩
        · rw [← h.1, ← h.2, (hfix a haF).2, (hfix a haF).1]
          exact Relation.ReflTransGen.single ⟨a, Finset.mem_erase.mpr ⟨haf, haF⟩, Or.inr ⟨rfl, rfl⟩⟩
    simpa only [(hfix f hfF).1, (hfix f hfF).2] using hm

theorem arrow_incident {a b : ULift.{0} V}
    (e : @Quiver.Hom (ULift.{0} V) (pathQuiver G) a b) (v : V) :
    G.left e.val = v ∨ G.right e.val = v ↔ ULift.up v = a ∨ ULift.up v = b := by
  rcases e.property with h | h
  · have hl : G.left e.val = a.down := congrArg (fun p => p.1.down) h
    have hr : G.right e.val = b.down := congrArg (fun p => p.2.down) h
    simp only [hl, hr, ULift.ext_iff, eq_comm]
  · have hl : G.left e.val = b.down := congrArg (fun p => p.1.down) h
    have hr : G.right e.val = a.down := congrArg (fun p => p.2.down) h
    simp only [hl, hr, ULift.ext_iff, eq_comm, or_comm]

theorem is_tree_insert_leaf {S : Set V} {F : Finset E} (hF : G.is_tree S F)
    {a b : ULift.{0} V} (e : @Quiver.Hom (ULift.{0} V) (pathQuiver G) a b)
    (hb : b.down ∈ S) (ha : a.down ∉ S) : G.is_tree (insert a.down S) (insert e.val F) := by
  have he : G.adjacent (insert e.val F) a.down b.down := by
    refine ⟨e.val, Finset.mem_insert_self _ _, ?_⟩
    rcases e.property with h | h
    · exact Or.inl ⟨congrArg (fun p => p.1.down) h, congrArg (fun p => p.2.down) h⟩
    · exact Or.inr ⟨congrArg (fun p => p.2.down) h, congrArg (fun p => p.1.down) h⟩
  have hreach (v : V) (hv : v ∈ insert a.down S) : G.reaches (insert e.val F) v b.down := by
    rcases hv with rfl | hv
    · exact Relation.ReflTransGen.single he
    · exact G.reaches_mono (Finset.subset_insert _ _) (hF.2.2.1 v hv b.down hb)
  refine ⟨hF.1.mono (Set.subset_insert _ _), ?_, ?_, ?_⟩
  · intro f hf
    rcases Finset.mem_insert.mp hf with hf | hf
    · subst f
      have hi (v : V) (hv : G.left e.val = v ∨ G.right e.val = v) : v ∈ insert a.down S := by
        rcases (arrow_incident G e v).mp hv with h | h
        · exact Or.inl (congrArg ULift.down h)
        · apply Or.inr
          have hvb : v = b.down := congrArg ULift.down h
          rw [hvb]
          exact hb
      exact ⟨hi _ (Or.inl rfl), hi _ (Or.inr rfl)⟩
    · exact ⟨Or.inr (hF.2.1 f hf).1, Or.inr (hF.2.1 f hf).2⟩
  · intro x hx y hy
    exact (hreach x hx).trans (G.reaches_symm (hreach y hy))
  · apply is_forest_insert_leaf G hF.2.2.2 e.val a.down
    · exact (arrow_incident G e _).mpr (Or.inl (ULift.up_down a))
    · intro f hf
      exact ⟨fun h => ha (h ▸ (hF.2.1 f hf).1), fun h => ha (h ▸ (hF.2.1 f hf).2)⟩

theorem is_tree_attach_path {a b : ULift.{0} V}
    (p : @Path (ULift.{0} V) (pathQuiver G) a b)
    (hp : (@Path.vertices _ (pathQuiver G) _ _ p).Nodup)
    (S : Set V) (F : Finset E) (hF : G.is_tree S F) (hb : b.down ∈ S)
    (hmeet : ∀ v ∈ @Path.vertices _ (pathQuiver G) _ _ p, v.down ∈ S → v = b) :
    G.is_tree (S ∪ {v | ULift.up v ∈ @Path.vertices _ (pathQuiver G) _ _ p}) (F ∪ pathCopies G p) := by
  letI := pathQuiver G
  induction p generalizing S F with
  | nil =>
    have he : S ∪ {v | ULift.up v ∈ (Path.nil : Path a a).vertices} = S := by
      ext v; simp only [Path.vertices, List.mem_singleton, ULift.ext_iff, Set.mem_union,
        Set.mem_setOf_eq]; exact ⟨fun h => h.elim id (fun h => h ▸ hb), Or.inl⟩
    simpa only [he, pathCopies, Finset.union_empty] using hF
  | @cons b c p e ih =>
    have hpair : c ∉ p.vertices ∧ p.vertices.Nodup := (List.nodup_concat _ _).mp hp
    have hbS : b.down ∉ S := by
      intro hm
      have he := hmeet b ((Path.mem_vertices_cons p e).mpr (Or.inl (Path.end_mem_vertices p))) hm
      exact hpair.1 (he ▸ Path.end_mem_vertices p)
    have ht := is_tree_insert_leaf G hF e hb hbS
    have hm : ∀ v ∈ p.vertices, v.down ∈ insert b.down S → v = b := by
      intro v hv hvs
      rcases hvs with hvs | hvs
      · exact ULift.ext_iff.mpr hvs
      · have he := hmeet v ((Path.mem_vertices_cons p e).mpr (Or.inl hv)) hvs
        exact False.elim (hpair.1 (he ▸ hv))
    have hi := ih hpair.2 (insert b.down S) (insert e.val F) ht (Set.mem_insert _ _) hm
    have hset : insert b.down S ∪ {v | ULift.up v ∈ p.vertices} =
        S ∪ {v | ULift.up v ∈ (p.cons e).vertices} := by
      ext v
      have hbm : ULift.up b.down ∈ p.vertices := by simp
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_setOf_eq, Path.mem_vertices_cons]
      constructor
      · rintro ((h | h) | h)
        · subst v; exact Or.inr (Or.inl hbm)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
        · apply Or.inl ∘ Or.inr
          have hvc : v = c.down := congrArg ULift.down h
          rw [hvc]
          exact hb
    rw [hset] at hi
    simpa only [pathCopies, Finset.union_insert, Finset.insert_union] using hi

end
end FiniteAvalanches.Wilson.CopiedNetwork
