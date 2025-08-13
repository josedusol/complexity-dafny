include "./ExpReal.dfy"
include "./Log2Nat.dfy"

/******************************************************************************
  Logarithm over reals
******************************************************************************/

module LogReal {
  import opened ExpReal
  import N = Log2Nat

  // log_b(x)
  // We assert lem_logIsNonNegative as post for convenience
  ghost function {:axiom} log(b:real, x:real) : real
    requires b > 1.0 && x > 0.0
    ensures  b > 1.0 && x >= 1.0 ==> log(b, x) >= 0.0

  // log_b(1) == 0
  lemma {:axiom} lem_logbOne(b:real)
    requires b > 1.0
    ensures  log(b, 1.0) == 0.0

  // b > 1 /\ x >= 1 ==> log_b(x) >= 0
  lemma {:axiom} lem_logIsNonNegative(b:real, x:real)
    requires b > 1.0 && x >= 1.0 
    ensures  log(b, x) >= 0.0

  // b > 1 /\ 0 < x <= y ==> log_b(x) <= log_b(y)
  lemma {:axiom} lem_logMonoIncr(b:real, x:real, y:real)
    requires b > 1.0 && x > 0.0 
    ensures  x <= y ==> log(b, x) <= log(b, y)

  // b1 > 1 /\ b2 > 1 /\ x >= 1 /\ b1 <= b2 ==> log_b1(x) >= log_b2(y)
  lemma {:axiom} lem_logBaseMonoDecr(b1:real, b2:real, x:real)
    requires b1 > 1.0 && b2 > 1.0 && x >= 1.0
    ensures  b1 <= b2 ==> log(b1, x) >= log(b2, x)    

  /* log_b(x) and b^x are inverses of each other */

  // log_b(b^x) = x 
  lemma {:axiom} lem_logAndExpInverse(b:real, x:real)
    requires b > 1.0
    requires exp(b, x) > 0.0
    ensures  log(b, exp(b, x)) == x 

  // b^(log_b(x)) = x 
  lemma {:axiom} lem_expAndLogInverse(b:real, x:real)
    requires b > 1.0 && x > 0.0
    ensures  exp(b, log(b, x)) == x

  // log_b(b) == 1.0
  lemma lem_logbOfb(b:real)
    requires b > 1.0
    ensures  log(b, b) == 1.0    
  {
    calc {
           true;
      <==> { lem_expOne(b); }
           exp(b, 1.0) == b;
      ==>  log(b, exp(b, 1.0)) == log(b, b);
      <==> { lem_logAndExpInverse(b, 1.0); }
           1.0 == log(b, b);
    }
  }
  
  // 1 < b <= x ==> log(b, x) >= 1
  lemma lem_logGEQone(b:real, x:real)
    requires 1.0 < b <= x
    ensures  log(b, x) >= 1.0
  {
    calc {
           b <= x;
      ==>  { lem_logMonoIncr(b, b, x); }
           log(b, x) >= log(b, b); 
      <==> { lem_logbOfb(b); }
           log(b, x) >= 1.0;
    }
  }  

  /******************************************************************************
    Special log_2(x)
  ******************************************************************************/

  // log_2(x)
  ghost function log2(x:real) : real
    requires x > 0.0
  { 
    log(2.0, x)
  }

  // 2 <= x ==> log(2, x) >= 1
  lemma lem_log2GEQone(x:real)
    requires 2.0 <= x
    ensures  log2(x) >= 1.0
  {
    lem_logGEQone(2.0, x);
  }  

  // Bound the real-valued log2 function with the natural-number version N.log2
  // N.log2(n) <= log2(n) < N.log2(n) + 1     where N.log2(n) = floor(log2(n))
  lemma lem_log2NatBounds(n:nat)
    requires n > 0
    ensures  N.log2(n) as real <= log2(n as real)
    ensures  log2(n as real) < (N.log2(n) + 1) as real
  {
    lem_log2NatLowBound(n);
    lem_log2NatUpBound(n);
  }

  // log2(n) < N.log2(n) + 1     where N.log2(n) = floor(log2(n))
  lemma {:axiom} lem_log2NatUpBound(n:nat)
    requires n > 0
    ensures  log2(n as real) < (N.log2(n) + 1) as real

  // N.log2(n) <= log2(n)        where N.log2(n) = floor(log2(n))
  lemma {:axiom} lem_log2NatLowBound(n:nat)
    requires n > 0
    ensures  N.log2(n) as real <= log2(n as real)

  /******************************************************************************
    Universal closures of lemmas
  ******************************************************************************/

  // b > 1 /\ x >= 1 ==> log_b(x) >= 0
  lemma lem_logIsNonNegativeAll()
    ensures  forall b:real, x:real :: 
             b > 1.0 && x >= 1.0 ==> log(b, x) >= 0.0
  {
    forall b:real, x:real | b > 1.0 && x >= 1.0 
      ensures log(b, x) >= 0.0
    {
      lem_logIsNonNegative(b, x);
    }    
  }

}