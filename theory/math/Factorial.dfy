
/**************************************************************************
  Factorial
**************************************************************************/

module Factorial {

  // !n
  opaque ghost function fac(n:nat) : nat
    decreases n
  {
    if n == 0 then 1 else n*fac(n-1)
  }

}