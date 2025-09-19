include "./Monoid.dfy"

/******************************************************************************
  Group structure (T,⊗,⁻¹,id) extends Monoid
******************************************************************************/

abstract module Group refines Monoid {

  // Introduce inverse operation 
  // _⁻¹ : T → T
  function inv(x:T): T

  // x⁻¹ ⊗ x = id
  lemma {:axiom} lem_LeftInverse(x:T)
    ensures op(inv(x), x) == id

  // x ⊗ x⁻¹ = id
  lemma {:axiom} lem_RightInverse(x:T)
    ensures op(x, inv(x)) == id

  // x ⊗ x⁻¹ = x⁻¹ ⊗ x = id
  lemma lem_Inverse(x:T) 
    ensures op(x, inv(x)) == op(inv(x), x) == id 
  {
    lem_LeftInverse(x);
    lem_RightInverse(x); 
  }

  lemma lem_InverseAuto()
    ensures forall x:T :: op(x, inv(x)) == op(inv(x), x) == id 
  {
    forall x:T ensures op(x, inv(x)) == op(inv(x), x) == id  {
      lem_Inverse(x);
    }
  }  

}