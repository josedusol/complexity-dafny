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

}

