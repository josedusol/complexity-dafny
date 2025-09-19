include "./TotalOrd.dfy"

/******************************************************************************
  (ℤ,<=) is a total order
******************************************************************************/

module OrdInt refines TotalOrd {

  type T = int

  ghost predicate Leq(x:T, y:T) { x <= y }

  // Prove everything that was considered an axiom before

  // x <= x
  lemma lem_Leq_Refl(x:T)
  { }

  // x <= y ∧ y <= z ⟹ x <= z
  lemma lem_Leq_Trans(x:T, y:T, z:T)
  { }
 
  // x <= y ∧ y <= x ⟹ x = y
  lemma lem_Leq_AntiSym(x:T, y:T)
  { }      

  // x ≠ y ⟹ x < y ∨ y < x
  lemma lem_Leq_Comparable(x:T, y:T)
  { }

  // x = y ⟹ x <= z
  lemma lem_Leq_SubstEq(x:T, y:T)
  { }

}  