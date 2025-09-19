include "./SemiGroup.dfy"

/******************************************************************************
  Monoid structure (T,⊗,id) extends SemiGroup
******************************************************************************/

abstract module Monoid refines SemiGroup {

  // Existence of an element of T that behaves as the monoid identity
  const id:T

  // id ⊗ x = x
  lemma {:axiom} lem_LeftIdentity(x:T) 
    ensures op(id, x) == x 

  // x ⊗ id = x
  lemma {:axiom} lem_RightIdentity(x:T) 
    ensures op(x, id) == x 

  // x ⊗ id = id ⊗ x = x
  lemma {:axiom} lem_Identity(x:T) 
    ensures op(x, id) == op(id, x) == x 
  {
    lem_LeftIdentity(x);
    lem_RightIdentity(x); 
  }

  lemma lem_IdentityAuto()
    ensures forall x:T :: op(x, id) == op(id, x) == x 
  {
    forall x:T ensures op(x, id) == op(id, x) == x {
      lem_Identity(x);
    }
  }    

}