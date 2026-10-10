import FiniteAvalanches.Wilson.NonemptyQuotient
import FiniteAvalanches.Trees.RootedForests
import FiniteAvalanches.Trees.Ancestors

/-! Literal copied-edge subset projection and lifting through a nonempty root quotient. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.CopiedNetwork.NonemptyQuotient
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)
  (R : CopiedNetwork.Roots (V := V))

/-- Select the surviving original copies in a prescribed family. -/
def projectCopies (F : Finset E) : Finset (Copy G R) :=
  Finset.univ.filter (fun e => e.val ∈ F)

/-- Lift copies by their individual original identities. -/
def liftCopies (t : Finset (Copy G R)) : Finset E := t.image Subtype.val

@[simp] theorem mem_projectCopies (F : Finset E) (e : Copy G R) :
    e ∈ projectCopies G R F ↔ e.val ∈ F := by simp [projectCopies]

@[simp] theorem mem_liftCopies (t : Finset (Copy G R)) (e : Copy G R) :
    e.val ∈ liftCopies G R t ↔ e ∈ t := by
  simp [liftCopies, Subtype.coe_injective.eq_iff]

@[simp] theorem project_lift_copies (t : Finset (Copy G R)) :
    projectCopies G R (liftCopies G R t) = t := by ext e; simp

theorem forest_copy_survives {F : Finset E} (hF : G.is_rooted_forest R.val F)
    (e : E) (he : e ∈ F) : project R (G.left e) ≠ project R (G.right e) := by
  intro h
  obtain ⟨hl, hr⟩ := (contracted_loop_iff G R e).mp h
  obtain ⟨r, _, _, hu⟩ := hF.2 (G.left e)
  have ha : G.left e = r := hu _ hl .refl
  have hb : G.right e = r := hu _ hr (.single ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩)
  exact G.loopless e (ha.trans hb.symm)

theorem lift_project_forest {F : Finset E} (hF : G.is_rooted_forest R.val F) :
    liftCopies G R (projectCopies G R F) = F := by
  ext e
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact (mem_projectCopies G R F f).mp hf
  · intro he
    exact Finset.mem_image.mpr ⟨⟨e, forest_copy_survives G R hF e he⟩, by simpa using he, rfl⟩

theorem reaches_project_copies {F : Finset E} {x y : V} (h : G.reaches F x y) :
    (graph G R).reaches (projectCopies G R F) (project R x) (project R y) := by
  apply Relation.ReflTransGen.lift' (project R) (fun u v he => ?_) _ _ h
  obtain ⟨e, he, h | h⟩ := he
  all_goals
    by_cases hs : project R (G.left e) = project R (G.right e)
    · have huv : project R u = project R v := by
        first
        | exact (congrArg (project R) h.1).symm.trans (hs.trans (congrArg (project R) h.2))
        | exact (congrArg (project R) h.1).symm.trans (hs.symm.trans (congrArg (project R) h.2))
      change (graph G R).reaches _ (project R u) (project R v)
      rw [huv]; exact .refl
    · exact .single ⟨⟨e, hs⟩, (mem_projectCopies G R F _).mpr he, by
        first
        | exact Or.inl ⟨congrArg (project R) h.1, congrArg (project R) h.2⟩
        | exact Or.inr ⟨congrArg (project R) h.1, congrArg (project R) h.2⟩⟩

theorem project_erase_lift_subset (t : Finset (Copy G R)) (e : Copy G R) :
    projectCopies G R ((liftCopies G R t).erase e.val) ⊆ t.erase e := by
  intro f hf
  have hm := (mem_projectCopies G R _ f).mp hf
  exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hm).1 (congrArg Subtype.val h),
    (mem_liftCopies G R t f).mp (Finset.mem_erase.mp hm).2⟩

end
end FiniteAvalanches.Wilson.CopiedNetwork.NonemptyQuotient
