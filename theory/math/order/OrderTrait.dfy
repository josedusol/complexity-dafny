/******************************************************************************
  Order stuff
******************************************************************************/

module OrderTrait {

  // Any type T implementing Ord<T> must provide a predicate Lt(_,_)
  // and prove it behaves as _<_
  
  trait {:ghost} Ord<T(==)> {

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

    // Relate < to =
 
    lemma {:axiom} lem_Lt_NotEq(x:T, y:T)
      requires Lt(x, y)
      ensures  x != y

    lemma {:axiom} lem_Lt_IfNotEq(x:T, y:T)
      requires x != y 
      ensures  Lt(x, y) || Lt(y, x)

  }

  // Implement Ord for nat

  class {:ghost} NatOrd extends Ord<nat> {

    ghost predicate Lt(x:nat, y:nat) {
      x < y
    }

    lemma lem_Lt_Irrfl(x:nat)
      ensures !Lt(x, x)
    { }

    lemma lem_Lt_Trans(x:nat, y:nat, z:nat)
      requires Lt(x, y) && Lt(y, z)
      ensures  Lt(x, z)
    { }

    lemma lem_Lt_Antisym(x:nat, y:nat)
      requires Lt(x, y)
      ensures  !(Lt(y, x))  
    { }  

    lemma lem_Lt_NotEq(x:nat, y:nat)
      requires Lt(x, y)
      ensures  x != y    
    { }

    lemma lem_Lt_IfNotEq(x:nat, y:nat)
      requires x != y 
      ensures  Lt(x, y) || Lt(y, x)   
    { } 

  }

  // Implement Ord for real

  class {:ghost} RealOrd extends Ord<real> {

    ghost predicate Lt(x:real, y:real) {
      x < y
    }

    lemma lem_Lt_Irrfl(x:real)
      ensures !Lt(x, x)
    { }

    lemma lem_Lt_Trans(x:real, y:real, z:real)
      requires Lt(x, y) && Lt(y, z)
      ensures  Lt(x, z)
    { }

    lemma lem_Lt_Antisym(x:real, y:real)
      requires Lt(x, y)
      ensures  !(Lt(y, x))  
    { }      


    lemma lem_Lt_NotEq(x:real, y:real)
      requires Lt(x, y)
      ensures  x != y    
    { }

    lemma lem_Lt_IfNotEq(x:real, y:real)
      requires x != y 
      ensures  Lt(x, y) || Lt(y, x)   
    { } 

  }  

}