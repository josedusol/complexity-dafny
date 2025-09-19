include "./IntervalMonoidPOrd.dfy"
include "../order/OrdReal.dfy"

/******************************************************************************
  Operation of (ℝ,+,0) on finite integer interval
******************************************************************************/

module IntervalSumReal refines IntervalMonoidPOrd {

  import Ord = OrdReal

  function op(x:T, y:T): T { x + y }

  const id:T := 0.0

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