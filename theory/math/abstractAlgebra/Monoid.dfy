include "./SemiGroup.dfy"

/******************************************************************************
  Monoid structure (T,⊗,id)
******************************************************************************/

abstract module Monoid refines SemiGroup {

  // Existence of an element of T that behaves as the monoid identity
  const id:T

  // x ⊗ id = id ⊗ x = x
  lemma {:axiom} lem_Identity(x:T) 
    ensures op(x, id) == op(id, x) == x 

  lemma lem_IdentityAuto()
    ensures forall x:T :: op(x, id) == op(id, x) == x 
  {
    forall x:T ensures op(x, id) == op(id, x) == x {
      lem_Identity(x);
    }
  }    

}