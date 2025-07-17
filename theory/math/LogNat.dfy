include "./ExpNat.dfy"

/**************************************************************************
  Base 2 logarithm over non-negative integers
**************************************************************************/

module LogNat {
  import opened ExpNat

  // log2(n) 
  opaque ghost function log2(n:nat) : nat
    requires  n > 0
    decreases n
  {
    if n == 1 then 0 else 1 + log2(n/2)
  }

  lemma lem_log2FirstValues()
    ensures log2(1) == 0
    ensures log2(2) == 1
    ensures log2(3) == 1
    ensures log2(4) == 2
    ensures log2(5) == 2
  {
    reveal log2();
  }

  // n>0 /\ m>0 /\ n <= m ==> log2(n) <= log2(m)
  lemma lem_log2Mono(n:nat, m:nat)
    requires n > 0 && m > 0
    ensures  n <= m ==> log2(n) <= log2(m)
    decreases n, m
  {
    reveal log2();
    if n != 1 && m != 1 { 
      lem_log2Mono(n-1, m-1); 
    }
  }

  /**************************************************************************
    log2(n) and 2^n are inverses of each other
    However, this holds only in a restricted sense because log2(n) is 
    in fact floor(log2(n)).
    So, in one direction we have the equality
      log2(2^n) == n 
    but in the other we only have the inequality
      2^log2(n) <= n
    unless n is an exact power of 2.
  **************************************************************************/

  // log2(2^n) = n 
  lemma lem_log2AndPow2Inverse(n:nat)
    requires exp(2,n) > 0
    ensures  log2(exp(2,n)) == n 
  {
    if n == 0 {
      // BC: n = 0
      calc {
          log2(exp(2,0));
        == { lem_exp2FirstValues(); }
          log2(1);
        == { lem_log2FirstValues(); }
          0;   
      }
    } else {
      // Step. n > 1
      //   IH: log2(2^(n-1)) = n-1 
      //    T: log2(2^n)     = n 
      calc {
          log2(exp(2, n));
        == { reveal exp(); }
          log2(2*exp(2, n-1));
        == { reveal log2(); }
          1 + log2(exp(2, n-1));
        == { lem_log2AndPow2Inverse(n-1); } // IH
          1 + (n - 1);
        == n;
      }
    }
  }

  // If n=2^k then log2(2^n)=n 
  lemma {:axiom} lem_exp2Andlog2Inverse(n:nat, k:nat)
    requires exp(2, k) > 0
    requires n == exp(2, k) 
    ensures exp(2, log2(n)) == n

}