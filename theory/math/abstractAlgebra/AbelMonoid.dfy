include "./Monoid.dfy"

/******************************************************************************
  Abelian Monoid structure (T,⊗,id) extends Monoid
******************************************************************************/

abstract module AbelMonoid refines Monoid {

  // x ⊗ y = y ⊗ x
  lemma {:axiom} lem_Commutative(x:T, y:T)
    ensures op(x, y) == op(y, x)

  lemma lem_CommutativeAuto()
    ensures forall x,y:T :: op(x, y) == op(y, x)
  {
    forall x,y:T ensures op(x, y) == op(y, x) {
      lem_Commutative(x, y);
    }
  }    

}