/******************************************************************************
  Order stuff
******************************************************************************/

module Order2 {

  // Any type T implementing Ord<T> must provide a predicate Lt(_,_)
  // and prove it behaves as _<_
  
  abstract module Ord {

    type T
 
    // x < y
    ghost predicate Lt(x:T, y:T)  

     // x > y
    ghost predicate Gt(x:T, y:T) { Lt(y, x) }

    // Minimal < properties

    lemma {:axiom} lem_Lt_Irrfl(x:T)
      ensures !Lt(x, x)

    lemma {:axiom} lem_Lt_Trans(x:T, y:T, z:T)
      requires Lt(x, y) && Lt(y, z)
      ensures  Lt(x, z)

    lemma {:axiom} lem_Lt_Antisym(x:T, y:T)
      requires Lt(x, y)
      ensures  !Lt(y, x)

    // Relate < to ==
 
    lemma {:axiom} lem_Lt_NotEq(x:T, y:T)
      requires Lt(x, y)
      ensures  x != y

    lemma {:axiom} lem_Lt_IfNotEq(x:T, y:T)
      requires x != y 
      ensures  Lt(x, y) || Lt(y, x)

  }

  // Implement Ord for nat

  module NatOrd refines Ord {

    type T = nat

    ghost predicate Lt(x:T, y:T) 
    {
      x < y
    }

    lemma lem_Lt_Irrfl(x:T)
    { }

    lemma lem_Lt_Trans(x:T, y:T, z:T)
    { }

    lemma lem_Lt_Antisym(x:T, y:T)
    { }      

    lemma lem_Lt_NotEq(x:T, y:T)
    { }

    lemma lem_Lt_IfNotEq(x:T, y:T)  
    { } 

  }  

  // Implement Ord for real

  module RealOrd refines Ord {

    type T = real

    ghost predicate Lt(x:T, y:T) 
    {
      x < y
    }

    lemma lem_Lt_Irrfl(x:T)
      ensures !Lt(x, x)
    { }

    lemma lem_Lt_Trans(x:T, y:T, z:T)
    { }

    lemma lem_Lt_Antisym(x:T, y:T)
    { }      

    lemma lem_Lt_NotEq(x:T, y:T)
    { }

    lemma lem_Lt_IfNotEq(x:T, y:T)
    { } 

  }  

}