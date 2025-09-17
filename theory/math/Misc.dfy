/******************************************************************************
  Miscelanious stuff
******************************************************************************/

module Misc {

  // apparently useless
  ghost function ite<T>(cond:bool, thenBranch:T, elseBranch:T) : T
  {
    if cond then thenBranch else elseBranch
  }

  // Dafny "{}" only works for the finite empty set.
  // This defines the infinite empty set for any type.
  ghost function emptyInfSet<T>() : iset<T> 
    ensures !exists x :: x in emptyInfSet<T>()
  {
    (iset x:T | x in {})
  }

}