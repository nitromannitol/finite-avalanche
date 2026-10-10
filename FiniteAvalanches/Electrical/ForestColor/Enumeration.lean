import FiniteAvalanches.Trees.ForestProjection.GramTransport
import Mathlib.LinearAlgebra.Matrix.Adjugate

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.ForestColor
open scoped Classical BigOperators Matrix
noncomputable section

variable {n : ℕ}

def rootPair (j : Fin (n + 1)) : Finset (Fin (n + 2)) := {0, j.succ}

theorem rootPair_card (j : Fin (n + 1)) : (rootPair j).card = 2 := by
  simp [rootPair, Ne.symm (Fin.succ_ne_zero j)]

theorem rootPair_compl_card (j : Fin (n + 1)) : (rootPair j)ᶜ.card = n := by
  rw [Finset.card_compl, Fintype.card_fin, rootPair_card]
  omega

theorem rootPair_enumeration (j : Fin (n + 1)) (i : Fin 2) :
    (rootPair j).orderEmbOfFin (rootPair_card j) i = if i = 0 then 0 else j.succ := by
  have h : (fun i : Fin 2 => if i = 0 then (0 : Fin (n + 2)) else j.succ) =
      (rootPair j).orderEmbOfFin (rootPair_card j) :=
    Finset.orderEmbOfFin_unique (rootPair_card j)
      (by intro i; split_ifs <;> simp [rootPair])
      (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all)
  exact (congrFun h i).symm

theorem rootPair_compl_enumeration (j : Fin (n + 1)) (k : Fin n) :
    (rootPair j)ᶜ.orderEmbOfFin (rootPair_compl_card j) k = (j.succAbove k).succ := by
  have h : (fun k : Fin n => (j.succAbove k).succ) =
      (rootPair j)ᶜ.orderEmbOfFin (rootPair_compl_card j) :=
    Finset.orderEmbOfFin_unique (rootPair_compl_card j)
      (by
        intro k
        simp only [Finset.mem_compl, rootPair, Finset.mem_insert, Finset.mem_singleton]
        rintro (h | h)
        · exact Fin.succ_ne_zero _ h
        · exact Fin.succAbove_ne j k (Fin.ext (Nat.succ.inj (congrArg Fin.val h))))
      (by intro a b hab; exact Fin.succ_lt_succ_iff.mpr ((Fin.strictMono_succAbove j) hab))
  exact (congrFun h k).symm

end
end FiniteAvalanches.Electrical.ForestColor
