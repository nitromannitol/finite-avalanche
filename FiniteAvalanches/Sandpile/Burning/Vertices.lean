module

public import FiniteAvalanches.Sandpile.Burning.SourceFields

@[expose] public section

/-! The two-phase field carriers identify every original active vertex with
exactly one nonsink vertex of the literal complement or held copied graph. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (s : V)

abbrev InsideVertex (A : Finset (SourceVertex s)) := {x : SourceVertex s // x ∈ A}
abbrev OutsideVertex (A : Finset (SourceVertex s)) := {x : SourceVertex s // x ∉ A}

def insideVertexEquiv (A : Finset (SourceVertex s)) :
    InsideVertex s A ≃ InducedVertex (A.image Subtype.val) where
  toFun x := ⟨x.val.val, Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩⟩
  invFun v :=
    let x : SourceVertex s := ⟨v.val, Finset.mem_erase.mpr
      ⟨by
        intro hv
        apply source_shape_avoids_sink s A
        simpa only [hv] using v.property, Finset.mem_univ _⟩⟩
    ⟨x, (subtype_mem_image_iff (Finset.univ.erase s) A x).mpr v.property⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv v := by apply Subtype.ext; rfl

@[simp] theorem inside_vertex_equiv_val (A : Finset (SourceVertex s)) (x : InsideVertex s A) :
    (insideVertexEquiv s A x).val = x.val.val := rfl

def someVertexEquiv {T : Type*} [Fintype T] [DecidableEq T] :
    T ≃ SourceVertex (none : Option T) where
  toFun v := ⟨some v, by simp⟩
  invFun v := match hv : v.val with
    | some x => x
    | none => False.elim (source_vertex_ne_sink none v hv)
  left_inv v := rfl
  right_inv v := by
    apply Subtype.ext
    rcases v with ⟨v, hv⟩
    cases v with
    | none => simp at hv
    | some x => rfl

@[simp] theorem some_vertex_equiv_val {T : Type*} [Fintype T] [DecidableEq T] (x : T) :
    (someVertexEquiv x).val = some x := rfl

def heldVertexEquiv (A : Finset (SourceVertex s)) :
    InsideVertex s A ≃ SourceVertex (none : Option (InducedVertex (A.image Subtype.val))) :=
  (insideVertexEquiv s A).trans someVertexEquiv

@[simp] theorem held_vertex_equiv_val (A : Finset (SourceVertex s)) (x : InsideVertex s A) :
    (heldVertexEquiv s A x).val = some (insideVertexEquiv s A x) := rfl

/-- The literal induced graph on D, including its original sink. -/
def complementGraph (A : Finset (SourceVertex s)) :=
  inducedGraph G (Finset.univ \ A.image Subtype.val)

def complementSink (A : Finset (SourceVertex s)) :
    InducedVertex (Finset.univ \ A.image Subtype.val) :=
  ⟨s, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, source_shape_avoids_sink s A⟩⟩

def outsideVertexEquiv (A : Finset (SourceVertex s)) :
    OutsideVertex s A ≃ SourceVertex (complementSink s A) where
  toFun x := ⟨⟨x.val.val, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hx =>
    x.property ((subtype_mem_image_iff (Finset.univ.erase s) A x.val).mpr hx)⟩⟩,
    Finset.mem_erase.mpr ⟨fun he => source_vertex_ne_sink s x.val (congrArg Subtype.val he),
      Finset.mem_univ _⟩⟩
  invFun v :=
    let x : SourceVertex s := ⟨v.val.val, Finset.mem_erase.mpr
      ⟨fun he => source_vertex_ne_sink (complementSink s A) v (Subtype.ext he), Finset.mem_univ _⟩⟩
    ⟨x, fun hx => (Finset.mem_sdiff.mp v.val.property).2
      ((subtype_mem_image_iff (Finset.univ.erase s) A x).mp hx)⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv v := by apply Subtype.ext; apply Subtype.ext; rfl

@[simp] theorem outside_vertex_equiv_val (A : Finset (SourceVertex s)) (x : OutsideVertex s A) :
    (outsideVertexEquiv s A x).val.val = x.val.val := rfl

end
end FiniteAvalanches.Sandpile.Burning
