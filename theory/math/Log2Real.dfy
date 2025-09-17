include "./LemFunction.dfy"
include "./LogReal.dfy"
include "./Log2Nat.dfy"

/******************************************************************************
  Base 2 logarithm over reals
******************************************************************************/

module Log2Real {

  import opened LemFunction
  import LR  = LogReal
  import L2N = Log2Nat

  // log_2(x)
  opaque ghost function log2(x:real) : real
    requires x > 0.0
    ensures  x >= 1.0 ==> log2(x) >= 0.0
  { 
    LR.lem_NonNegativeAuto();
    LR.log(2.0, x)
  }

  // x >= 2 ⟹ log2(x) >= 1
  lemma lem_GEQone(x:real)
    requires x >= 2.0
    ensures  log2(x) >= 1.0
  {
    reveal log2();
    LR.lem_GEQone(2.0, x);
  }  

  // Bound the real-valued log2 function with the natural-number version N.log2
  // N.log2(n) <= log2(n) < N.log2(n) + 1     where N.log2(n) = floor(log2(n))
  lemma lem_NatBounds(n:nat)
    requires n > 0
    ensures  L2N.log2(n) as real <= log2(n as real)
    ensures  log2(n as real) < (L2N.log2(n) + 1) as real
  {
    lem_NatLowBound(n);
    lem_NatUpBound(n);
  }

  // log2(n) < N.log2(n) + 1     where N.log2(n) = floor(log2(n))
  lemma {:axiom} lem_NatUpBound(n:nat)
    requires n > 0
    ensures  log2(n as real) < (L2N.log2(n) + 1) as real

  // N.log2(n) <= log2(n)        where N.log2(n) = floor(log2(n))
  lemma {:axiom} lem_NatLowBound(n:nat)
    requires n > 0
    ensures  L2N.log2(n) as real <= log2(n as real)

}