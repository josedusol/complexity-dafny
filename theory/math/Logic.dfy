/******************************************************************************
  Logic stuf
******************************************************************************/

module Logic {

  // (∃!x)P(x) quantifier
  ghost predicate ExistsOne<T(!new)>(P:T->bool)
  {
       (exists x :: P(x))
    && (forall y, z :: P(y) && P(z) ==> y == z)
  }

  ghost predicate xor(a:bool, b:bool) {
    (a && !b) || (!a && b)
  }

  ghost predicate xor3(a:bool, b:bool, c:bool) {
    (a && !b && !c) || (!a && b && !c) || (!a && !b && c)
  }  

}

