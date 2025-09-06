
/******************************************************************************
  Factorial
******************************************************************************/

module Factorial {

  // !n
  opaque ghost function fac(n:nat) : nat
    decreases n
  {
    if n == 0 then 1 else n*fac(n-1)
  }

  lemma lem_fac_FirstValues()
    ensures fac(0) == 1
    ensures fac(1) == 1
    ensures fac(2) == 2
    ensures fac(3) == 6
    ensures fac(4) == 24
  {
    reveal fac();
  }

}