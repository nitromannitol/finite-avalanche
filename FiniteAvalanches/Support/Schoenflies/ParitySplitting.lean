/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/ParitySplitting.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.PolygonalJordan
import FiniteAvalanches.Support.Schoenflies.OverlayGraph

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 





















































































open Metric Set

namespace Schoenflies

variable {u p q r : Plane} {L L₁ L₂ L₃ : List Piece} {m : ℕ}

 





 

theorem not_crosses_of_level {c d : Plane} (h : hgt u c = hgt u d) (q : Plane) :
    ¬ Crosses u (c, d) q := by
  intro hcr
  obtain ⟨h1, h2, -⟩ := hcr
  have e1 : ((c, d) : Piece).1 = c := rfl
  have e2 : ((c, d) : Piece).2 = d := rfl
  rw [e1, e2, h, min_self] at h1
  rw [e1, e2, h, max_self] at h2
  linarith

 


theorem mark_swap' (u : Plane) (P : Piece) (q : Plane) : mark u (P.2, P.1) q = mark u P q := by
  obtain ⟨a, b⟩ := P
  by_cases h : hgt u a = hgt u b
  · rw [mark, mark, if_neg (not_crosses_of_level h.symm q), if_neg (not_crosses_of_level h q)]
  · exact mark_swap h q

 
theorem parity_perm (h : L₁.Perm L₂) (u q : Plane) : parity u L₁ q = parity u L₂ q :=
  (h.map fun P => mark u P q).sum_eq

 
theorem cover_perm (h : L₁.Perm L₂) : cover L₁ = cover L₂ := by
  ext z
  simp only [cover, mem_iUnion, exists_prop]
  exact ⟨fun ⟨P, hP, hz⟩ => ⟨P, h.mem_iff.1 hP, hz⟩, fun ⟨P, hP, hz⟩ => ⟨P, h.mem_iff.2 hP, hz⟩⟩

 
theorem orientPiece_eq_or (P : Piece) : orientPiece P = P ∨ orientPiece P = (P.2, P.1) := by
  by_cases h : Precedes P.1 P.2
  · exact Or.inl (orientPiece_of_precedes h)
  · exact Or.inr (orientPiece_of_not_precedes h)

theorem mark_orientPiece (u : Plane) (P : Piece) (q : Plane) :
    mark u (orientPiece P) q = mark u P q := by
  rcases orientPiece_eq_or P with h | h
  · rw [h]
  · rw [h, mark_swap']

theorem parity_map_orientPiece (u : Plane) (L : List Piece) (q : Plane) :
    parity u (L.map orientPiece) q = parity u L q := by
  simp only [parity, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun P _ => mark_orientPiece u P q)

theorem hgt_ne_orientPiece {P : Piece} (h : hgt u P.1 ≠ hgt u P.2) :
    hgt u (orientPiece P).1 ≠ hgt u (orientPiece P).2 := by
  rcases orientPiece_eq_or P with e | e
  · rw [e]; exact h
  · rw [e]; exact fun hh => h hh.symm

theorem hgt_ne_of_orientPiece {P : Piece} (h : hgt u (orientPiece P).1 ≠ hgt u (orientPiece P).2) :
    hgt u P.1 ≠ hgt u P.2 := by
  rcases orientPiece_eq_or P with e | e
  · rw [e] at h; exact h
  · rw [e] at h; exact fun hh => h hh.symm

 
theorem chainSum_map_orientPiece (f : Plane → ZMod 2) (L : List Piece) :
    ((L.map orientPiece).map fun P => f P.1 + f P.2).sum
      = (L.map fun P => f P.1 + f P.2).sum := by
  simp only [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun P _ => ?_)
  rcases orientPiece_eq_or P with e | e
  · rw [Function.comp_apply, e]
  · rw [Function.comp_apply, e]; exact add_comm _ _

 



def SameEdges (L₁ L₂ : List Piece) : Prop := (L₁.map orientPiece).Perm (L₂.map orientPiece)

@[refl] theorem SameEdges.refl (L : List Piece) : SameEdges L L := List.Perm.refl _

theorem SameEdges.symm (h : SameEdges L₁ L₂) : SameEdges L₂ L₁ := List.Perm.symm h

theorem SameEdges.trans (h₁ : SameEdges L₁ L₂) (h₂ : SameEdges L₂ L₃) : SameEdges L₁ L₃ :=
  List.Perm.trans h₁ h₂

 
theorem SameEdges.of_perm (h : L₁.Perm L₂) : SameEdges L₁ L₂ := h.map _

theorem SameEdges.append {L₁' L₂' : List Piece} (h₁ : SameEdges L₁ L₁') (h₂ : SameEdges L₂ L₂') :
    SameEdges (L₁ ++ L₂) (L₁' ++ L₂') := by
  simpa only [SameEdges, List.map_append] using List.Perm.append h₁ h₂

theorem sameEdges_reverse (L : List Piece) : SameEdges L.reverse L :=
  SameEdges.of_perm (List.reverse_perm L)

 

theorem sameEdges_map_swap (L : List Piece) : SameEdges (L.map fun P => (P.2, P.1)) L := by
  have : (L.map fun P => (P.2, P.1)).map orientPiece = L.map orientPiece := by
    rw [List.map_map]
    exact List.map_congr_left fun P _ => orientPiece_swap P
  rw [SameEdges, this]

 



theorem sameEdges_of_perm_reverse_swap {L A K : List Piece}
    (h : L.Perm (A ++ (K.map fun P => (P.2, P.1)).reverse)) : SameEdges L (A ++ K) :=
  (SameEdges.of_perm h).trans
    (SameEdges.append (SameEdges.refl A) ((sameEdges_reverse _).trans (sameEdges_map_swap K)))

theorem SameEdges.parity_eq (h : SameEdges L₁ L₂) (u q : Plane) :
    parity u L₁ q = parity u L₂ q := by
  rw [← parity_map_orientPiece u L₁ q, ← parity_map_orientPiece u L₂ q]
  exact parity_perm h u q

theorem SameEdges.cover_eq (h : SameEdges L₁ L₂) : cover L₁ = cover L₂ := by
  rw [← cover_map_orientPiece L₁, ← cover_map_orientPiece L₂]
  exact cover_perm h

 
theorem SameEdges.exists_mem (h : SameEdges L₁ L₂) {Q : Piece} (hQ : Q ∈ L₁) :
    ∃ R ∈ L₂, orientPiece R = orientPiece Q := by
  have hmem : orientPiece Q ∈ L₂.map orientPiece :=
    h.mem_iff.1 (List.mem_map_of_mem (f := orientPiece) hQ)
  obtain ⟨R, hR, hRQ⟩ := List.mem_map.1 hmem
  exact ⟨R, hR, hRQ⟩

 
theorem SameEdges.hgt_ne (h : SameEdges L₁ L₂) (hL : ∀ Q ∈ L₂, hgt u Q.1 ≠ hgt u Q.2) :
    ∀ Q ∈ L₁, hgt u Q.1 ≠ hgt u Q.2 := by
  intro Q hQ
  obtain ⟨R, hR, hRQ⟩ := h.exists_mem hQ
  exact hgt_ne_of_orientPiece (hRQ ▸ hgt_ne_orientPiece (hL R hR))

theorem hgt_ne_append (h₁ : ∀ Q ∈ L₁, hgt u Q.1 ≠ hgt u Q.2)
    (h₂ : ∀ Q ∈ L₂, hgt u Q.1 ≠ hgt u Q.2) : ∀ Q ∈ L₁ ++ L₂, hgt u Q.1 ≠ hgt u Q.2 := by
  intro Q hQ
  rcases List.mem_append.1 hQ with h | h
  · exact h₁ Q h
  · exact h₂ Q h

 






 

def IsChainFrom (L : List Piece) (p q : Plane) : Prop :=
  ∀ f : Plane → ZMod 2, (L.map fun P => f P.1 + f P.2).sum = f p + f q

 
theorem isChainFrom_self_iff : IsChainFrom L p p ↔ IsClosedChain L := by
  constructor <;> intro h f
  · rw [h f]; exact add_self_zmod_two _
  · rw [h f]; exact (add_self_zmod_two _).symm

theorem isChainFrom_nil (p : Plane) : IsChainFrom [] p p := fun f => by
  simp [(add_self_zmod_two (f p)).symm]

 
theorem IsChainFrom.append (h₁ : IsChainFrom L₁ p q) (h₂ : IsChainFrom L₂ q r) :
    IsChainFrom (L₁ ++ L₂) p r := by
  intro f
  rw [List.map_append, List.sum_append, h₁ f, h₂ f]
  linear_combination add_self_zmod_two (f q)

 

theorem IsChainFrom.isClosedChain_append (h₁ : IsChainFrom L₁ p q) (h₂ : IsChainFrom L₂ p q) :
    IsClosedChain (L₁ ++ L₂) := by
  intro f
  rw [List.map_append, List.sum_append, h₁ f, h₂ f]
  exact add_self_zmod_two _

theorem SameEdges.isChainFrom (h : SameEdges L₁ L₂) (h₂ : IsChainFrom L₂ p q) :
    IsChainFrom L₁ p q := by
  intro f
  rw [← chainSum_map_orientPiece f L₁, (h.map fun P => f P.1 + f P.2).sum_eq,
    chainSum_map_orientPiece, h₂ f]

theorem SameEdges.isClosedChain (h : SameEdges L₁ L₂) (h₂ : IsClosedChain L₂) :
    IsClosedChain L₁ := by
  intro f
  rw [← chainSum_map_orientPiece f L₁, (h.map fun P => f P.1 + f P.2).sum_eq,
    chainSum_map_orientPiece, h₂ f]

 




 
def pathPieces : List Plane → List Piece
  | [] => []
  | [_] => []
  | v :: w :: rest => (v, w) :: pathPieces (w :: rest)

@[simp] theorem pathPieces_nil : pathPieces [] = [] := rfl

@[simp] theorem pathPieces_singleton (v : Plane) : pathPieces [v] = [] := rfl

@[simp] theorem pathPieces_cons_cons (v w : Plane) (rest : List Plane) :
    pathPieces (v :: w :: rest) = (v, w) :: pathPieces (w :: rest) := rfl

 
theorem isChainFrom_pathPieces (p : Plane) (mid : List Plane) (q : Plane) :
    IsChainFrom (pathPieces (p :: (mid ++ [q]))) p q := by
  induction mid generalizing p with
  | nil =>
    intro f
    simp
  | cons w ws ih =>
    intro f
    rw [List.cons_append, pathPieces_cons_cons, List.map_cons, List.sum_cons, ih w f]
    linear_combination add_self_zmod_two (f w)

 
theorem cover_pathPieces (p : Plane) (mid : List Plane) (q : Plane) :
    cover (pathPieces (p :: (mid ++ [q]))) = poly (p :: (mid ++ [q])) := by
  induction mid generalizing p with
  | nil =>
    rw [List.nil_append, pathPieces_cons_cons, pathPieces_singleton, cover_cons, cover_nil,
      poly_cons_cons, poly_singleton, union_empty]
    exact (union_eq_self_of_subset_right
      (singleton_subset_iff.2 (right_mem_segment ℝ p q))).symm
  | cons w ws ih =>
    rw [List.cons_append, pathPieces_cons_cons, cover_cons, ih w, poly_cons_cons]
    rfl

 






namespace ClosedPolygon

variable {C : ClosedPolygon m} {a : ZMod (m + 3)} {k : ℕ}

 


def arcPieces (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) : List Piece :=
  (List.range k).map fun t : ℕ => (C.vertex (a + t), C.vertex (a + t + 1))

@[simp] theorem arcPieces_zero (C : ClosedPolygon m) (a : ZMod (m + 3)) :
    C.arcPieces a 0 = [] := rfl

 
theorem arcPieces_add (C : ClosedPolygon m) (a : ZMod (m + 3)) (k l : ℕ) :
    C.arcPieces a (k + l) = C.arcPieces a k ++ C.arcPieces (a + k) l := by
  rw [arcPieces, arcPieces, arcPieces, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply, Nat.cast_add, ← add_assoc]

 
theorem arcPieces_full (C : ClosedPolygon m) : C.arcPieces 0 (m + 3) = C.pieces := by
  rw [arcPieces, pieces]
  exact List.map_congr_left fun t _ => by rw [zero_add]

 
theorem mem_pieces_of_mem_arcPieces {Q : Piece} (hQ : Q ∈ C.arcPieces a k) : Q ∈ C.pieces := by
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hQ
  exact C.mem_pieces _

theorem arcPieces_nondeg (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    ∀ Q ∈ C.arcPieces a k, Q.Nondeg :=
  fun _ hQ => C.pieces_nondeg _ (mem_pieces_of_mem_arcPieces hQ)

theorem arcPieces_hgt_ne (hL : ∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2) :
    ∀ Q ∈ C.arcPieces a k, hgt u Q.1 ≠ hgt u Q.2 :=
  fun _ hQ => hL _ (mem_pieces_of_mem_arcPieces hQ)

 

theorem isChainFrom_arcPieces (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    IsChainFrom (C.arcPieces a k) (C.vertex a) (C.vertex (a + k)) := by
  intro f
  have hmap : ((C.arcPieces a k).map fun P => f P.1 + f P.2)
      = (List.range k).map fun j : ℕ =>
          f (C.vertex (a + (j : ZMod (m + 3))))
            + f (C.vertex (a + ((j + 1 : ℕ) : ZMod (m + 3)))) := by
    rw [arcPieces, List.map_map]
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, natCast_succ, ← add_assoc]
  have key := sum_range_boundary (fun i : ℕ => f (C.vertex (a + (i : ZMod (m + 3))))) k
  rw [hmap, key]
  simp

 

theorem arcPieces_full_perm (C : ClosedPolygon m) (a : ZMod (m + 3)) :
    (C.arcPieces a (m + 3)).Perm C.pieces := by
  have hlt : a.val < m + 3 := ZMod.val_lt a
  have hcast : ((a.val : ℕ) : ZMod (m + 3)) = a := ZMod.natCast_rightInverse a
  
  have hzero : a + ((m + 3 - a.val : ℕ) : ZMod (m + 3)) = 0 := by
    rw [Nat.cast_sub hlt.le, hcast]
    simp
  have hsplit1 : C.arcPieces a (m + 3)
      = C.arcPieces a (m + 3 - a.val) ++ C.arcPieces 0 a.val := by
    have h1 : (m + 3 - a.val) + a.val = m + 3 := by omega
    have h2 := arcPieces_add C a (m + 3 - a.val) a.val
    rwa [h1, hzero] at h2
  have hsplit2 : C.pieces = C.arcPieces 0 a.val ++ C.arcPieces a (m + 3 - a.val) := by
    have h1 : a.val + (m + 3 - a.val) = m + 3 := by omega
    have h2 := arcPieces_add C 0 a.val (m + 3 - a.val)
    rw [h1, arcPieces_full, zero_add, hcast] at h2
    exact h2
  rw [hsplit1, hsplit2]
  exact List.perm_append_comm

 

theorem arcPieces_split_perm (C : ClosedPolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    (C.arcPieces a k ++ C.arcPieces (a + k) (m + 3 - k)).Perm C.pieces := by
  rw [← arcPieces_add, Nat.add_sub_cancel' hk]
  exact arcPieces_full_perm C a

theorem sameEdges_arcPieces_split (C : ClosedPolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    SameEdges C.pieces (C.arcPieces a k ++ C.arcPieces (a + k) (m + 3 - k)) :=
  SameEdges.of_perm (arcPieces_split_perm C a hk).symm

 
theorem cover_arcPieces_union (C : ClosedPolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    cover (C.arcPieces a k) ∪ cover (C.arcPieces (a + k) (m + 3 - k)) = C.carrier := by
  rw [← cover_append, cover_perm (arcPieces_split_perm C a hk), cover_pieces]

theorem cover_arcPieces_subset (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    cover (C.arcPieces a k) ⊆ C.carrier := by
  intro z hz
  obtain ⟨R, hR, hzR⟩ := exists_of_mem_cover hz
  rw [← cover_pieces]
  exact mem_cover (mem_pieces_of_mem_arcPieces hR) hzR

 

theorem isClosedChain_arcPieces_append {K : List Piece}
    (hK : IsChainFrom K (C.vertex a) (C.vertex (a + k))) :
    IsClosedChain (C.arcPieces a k ++ K) :=
  (isChainFrom_arcPieces C a k).isClosedChain_append hK

theorem arcPieces_append_hgt_ne {K : List Piece}
    (hC : ∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2) (hK : ∀ Q ∈ K, hgt u Q.1 ≠ hgt u Q.2) :
    ∀ Q ∈ C.arcPieces a k ++ K, hgt u Q.1 ≠ hgt u Q.2 :=
  hgt_ne_append (arcPieces_hgt_ne hC) hK

 

theorem carrier_eq_of_sameEdges {m' : ℕ} {J : ClosedPolygon m'} {K : List Piece}
    (h : SameEdges J.pieces (C.arcPieces a k ++ K)) :
    J.carrier = cover (C.arcPieces a k) ∪ cover K := by
  rw [← cover_pieces, h.cover_eq, cover_append]

 

theorem notMem_carrier_of_sameEdges {m' : ℕ} {J : ClosedPolygon m'} {K : List Piece}
    (h : SameEdges J.pieces (C.arcPieces a k ++ K)) {x : Plane} (hxC : x ∉ C.carrier)
    (hxK : x ∉ cover K) : x ∉ J.carrier := by
  rw [carrier_eq_of_sameEdges h]
  rintro (hx | hx)
  · exact hxC (cover_arcPieces_subset C a k hx)
  · exact hxK hx

end ClosedPolygon

 




 





theorem parity_split (u : Plane) {LC A₁ A₂ K : List Piece}
    (hC : SameEdges LC (A₁ ++ A₂)) (h₁ : SameEdges L₁ (A₁ ++ K)) (h₂ : SameEdges L₂ (A₂ ++ K))
    (q : Plane) : parity u L₁ q + parity u L₂ q = parity u LC q := by
  rw [h₁.parity_eq u q, h₂.parity_eq u q, hC.parity_eq u q, parity_append, parity_append,
    parity_append]
  linear_combination add_self_zmod_two (parity u K q)

namespace ClosedPolygon

variable {C : ClosedPolygon m} {a : ZMod (m + 3)} {k : ℕ}

 





theorem parity_splitting (C : ClosedPolygon m) (u : Plane) (a : ZMod (m + 3)) (hk : k ≤ m + 3)
    {K : List Piece} (h₁ : SameEdges L₁ (C.arcPieces a k ++ K))
    (h₂ : SameEdges L₂ (C.arcPieces (a + k) (m + 3 - k) ++ K)) (q : Plane) :
    parity u L₁ q + parity u L₂ q = parity u C.pieces q :=
  parity_split u (sameEdges_arcPieces_split C a hk) h₁ h₂ q

 





 

theorem parity_eq_one_iff (C : ClosedPolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2) {x : Plane} (hx : x ∉ C.carrier) :
    parity u C.pieces x = 1 ↔ x ∈ inside C.carrier := by
  have hmem : x ∈ inside C.carrier ∪ outside C.carrier := by
    rw [inside_union_outside]; exact hx
  refine ⟨fun h => ?_, C.parity_eq_one_of_mem_inside hu hL⟩
  rcases hmem with h' | h'
  · exact h'
  · rw [C.parity_eq_zero_of_mem_outside hu hL h'] at h
    exact absurd h (by decide)

 





theorem crosscut_inside_exactly_one {m₁ m₂ : ℕ} (C : ClosedPolygon m) (J₁ : ClosedPolygon m₁)
    (J₂ : ClosedPolygon m₂) {u : Plane} (hu : Plane.IsDirection u)
    (hC : ∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2) {K : List Piece}
    (hK : ∀ Q ∈ K, hgt u Q.1 ≠ hgt u Q.2) (hk : k ≤ m + 3)
    (h₁ : SameEdges J₁.pieces (C.arcPieces a k ++ K))
    (h₂ : SameEdges J₂.pieces (C.arcPieces (a + k) (m + 3 - k) ++ K))
    {x : Plane} (hx : x ∈ inside C.carrier) (hxK : x ∉ cover K) :
    x ∈ inside J₁.carrier ↔ x ∉ inside J₂.carrier := by
  have hJ₁ := h₁.hgt_ne (arcPieces_append_hgt_ne hC hK)
  have hJ₂ := h₂.hgt_ne (arcPieces_append_hgt_ne hC hK)
  have hsum := C.parity_splitting u a hk h₁ h₂ x
  rw [C.parity_eq_one_of_mem_inside hu hC hx] at hsum
  have harith : ∀ s t : ZMod 2, s + t = 1 → (s = 1 ↔ ¬ t = 1) := by decide
  rw [← J₁.parity_eq_one_iff hu hJ₁ (notMem_carrier_of_sameEdges h₁ hx.1 hxK),
    ← J₂.parity_eq_one_iff hu hJ₂ (notMem_carrier_of_sameEdges h₂ hx.1 hxK)]
  exact harith _ _ hsum

 


theorem crosscut_outside_agree {m₁ m₂ : ℕ} (C : ClosedPolygon m) (J₁ : ClosedPolygon m₁)
    (J₂ : ClosedPolygon m₂) {u : Plane} (hu : Plane.IsDirection u)
    (hC : ∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2) {K : List Piece}
    (hK : ∀ Q ∈ K, hgt u Q.1 ≠ hgt u Q.2) (hk : k ≤ m + 3)
    (h₁ : SameEdges J₁.pieces (C.arcPieces a k ++ K))
    (h₂ : SameEdges J₂.pieces (C.arcPieces (a + k) (m + 3 - k) ++ K))
    {x : Plane} (hx : x ∈ outside C.carrier) (hxK : x ∉ cover K) :
    x ∈ inside J₁.carrier ↔ x ∈ inside J₂.carrier := by
  have hJ₁ := h₁.hgt_ne (arcPieces_append_hgt_ne hC hK)
  have hJ₂ := h₂.hgt_ne (arcPieces_append_hgt_ne hC hK)
  have hsum := C.parity_splitting u a hk h₁ h₂ x
  rw [C.parity_eq_zero_of_mem_outside hu hC hx] at hsum
  have harith : ∀ s t : ZMod 2, s + t = 0 → (s = 1 ↔ t = 1) := by decide
  rw [← J₁.parity_eq_one_iff hu hJ₁ (notMem_carrier_of_sameEdges h₁ hx.1 hxK),
    ← J₂.parity_eq_one_iff hu hJ₂ (notMem_carrier_of_sameEdges h₂ hx.1 hxK)]
  exact harith _ _ hsum

end ClosedPolygon

end Schoenflies
