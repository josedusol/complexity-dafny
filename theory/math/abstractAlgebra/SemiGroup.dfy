include "./Magma.dfy"

/******************************************************************************
  Semi Group structure (T,⊗) extends Magma
******************************************************************************/

abstract module SemiGroup refines Magma {

  // x ⊗ (y ⊗ z) = (x ⊗ y) ⊗ z
  lemma {:axiom} lem_Associative(x:T, y:T, z:T)
    ensures op(x, op(y, z)) == op(op(x, y), z)

  lemma lem_AssociativeAuto()
    ensures forall x,y,z:T :: op(x, op(y, z)) == op(op(x, y), z)
  {
    forall x,y,z:T ensures op(x, op(y, z)) == op(op(x, y), z) {
      lem_Associative(x, y, z);
    }
  }    

}