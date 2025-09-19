include "./IntervalMonoidPOrd.dfy"
include "../order/OrdInt.dfy"

/******************************************************************************
  Operation of (ℤ,+,0) on finite integer interval
******************************************************************************/

module IntervalSumInt refines IntervalMonoidPOrd {

  import Ord = OrdInt

  function op(x:T, y:T): T { x + y }

  const id:T := 0

  lemma lem_Associative(x:T, y:T, z:T)
    ensures op(x, op(y,z)) == op(op(x,y), z)
  { }

  lemma lem_LeftIdentity(x:T) 
    ensures op(id, x) == x 
  { }

  lemma lem_RightIdentity(x:T) 
    ensures op(x, id) == x 
  { }  

}