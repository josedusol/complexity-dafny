include "../order/PartialOrd.dfy"
include "./Monoid.dfy"

/******************************************************************************
  Partially ordered monoid
******************************************************************************/

abstract module MonoidPOrd refines Monoid {

  import Ord : PartialOrd 

  // T now carries two structures: algebraic (T,⊗,id) and order (T,<=)
  type T = Ord.T

  /******************************************************************************
    Compatibility of = wrt (T,⊗,id) 
  ******************************************************************************/

  // Congruence
  // This is trivially provable in Dafny since functions are already extensional
  // x = x' ∧ y = y' ⟹ x ⊗ y = x' ⊗ y'
  lemma lem_Cong(x:T, x':T, y:T, y':T)
    requires x == x' && y == y'
    ensures  op(x, y) == op(x', y')
  { }

  lemma lem_CongAuto()
    ensures forall x,x',y,y':T :: x == x' && y == y' ==> op(x, y) == op(x', y')
  {
    forall x,x',y,y':T | x == x' && y == y'
      ensures op(x, y) == op(x', y')  
    {
      lem_Cong(x, x', y, y');
    }
  }   

  /******************************************************************************
    Compatibility of (T,<=) wrt (T,⊗,id) 
  ******************************************************************************/

  // Monoid operation is monotone on both arguments
  // i.e. if x ≤ y then operation with the same z on both sides preserves order
  // x <= y ⟹ x ⊗ z <= y ⊗ z
  //         ∧ z ⊗ x <= z ⊗ y
  lemma {:axiom} lem_Leq_Mono(x:T, y:T, z:T)
    requires Ord.Leq(x, y)
    ensures  Ord.Leq(op(x, z), op(y, z))
    ensures  Ord.Leq(op(z, x), op(z, y))  

  lemma lem_Leq_MonoAuto()
    ensures forall x,y,z:T :: 
      Ord.Leq(x, y) ==> Ord.Leq(op(x, z), op(y, z)) && Ord.Leq(op(z, x), op(z, y))  
  {
    forall x,y,z:T | Ord.Leq(x, y)
      ensures Ord.Leq(op(x, z), op(y, z)) && Ord.Leq(op(z, x), op(z, y))  
    {
      lem_Leq_Mono(x, y, z);
    }
  }  

  /******************************************************************************
    Compatibility of strict version (T,<) wrt (T,⊗,id) 
  ******************************************************************************/  

  // We have weak monotonicity for <, readily derivable from <=
  // x < y ⟹ x ⊗ z <= y ⊗ z
  //        ∧ z ⊗ x <= z ⊗ y
  lemma lem_Lt_WeakMono(x:T, y:T, z:T)
    requires Ord.Lt(x, y)
    ensures  Ord.Leq(op(x, z), op(y, z))
    ensures  Ord.Leq(op(z, x), op(z, y))  
  { 
    lem_Leq_MonoAuto();
  }

  lemma lem_Lt_WeakMonoAuto()
    ensures forall x,y,z:T :: 
      Ord.Lt(x, y) ==> Ord.Leq(op(x, z), op(y, z)) && Ord.Leq(op(z, x), op(z, y))  
  {
    forall x,y,z:T | Ord.Lt(x, y)
      ensures Ord.Leq(op(x, z), op(y, z)) && Ord.Leq(op(z, x), op(z, y))  
    {
      lem_Lt_WeakMono(x, y, z);
    }
  }  

}