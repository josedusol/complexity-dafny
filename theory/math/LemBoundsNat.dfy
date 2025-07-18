
include "./ExpNat.dfy"
include "./LogNat.dfy"

/**************************************************************************
  Bounds of mathematical functions over non-negative integers
**************************************************************************/

module LemBoundsNat {
  import opened ExpNat
  import opened LogNat

  // n > 0 ==> 2^log2(n) <= n
  lemma lem_log2exp2_bounds(n:nat)
    requires n > 0
    ensures  exp(2, log2(n)) <= n
  {
    if n == 1 {
      // BC: n = 1
      calc {
           exp(2, log2(1));
        == { lem_log2FirstValues(); }
           exp(2, 0);
        == { lem_exp2FirstValues(); }
           1;   
      }
    } else {
      // Step. n > 1
      //   IH: 2^log2(n/2) <= n/2
      //    T:   2^log2(n) <= n
      assert log2(n) >= 1 by { reveal log2(); }
      // Note that by the definition
      assert A: log2(n)-1 <= log2(n/2) by { reveal log2(); }
      calc {
           exp(2, log2(n));
        == { reveal exp(); }
           2*exp(2, log2(n)-1);
        <= { reveal A; lem_expMono(2, log2(n)-1, log2(n/2)); }
           2*exp(2, log2(n/2));
        <= { lem_log2exp2_bounds(n/2); }
           2*(n/2);
        <= n;
      }
    }
  }

  // n > 0 ==> n < 2^(log2(n)+1)
  lemma lem_nLQexp2log2nPlus1(n:nat)
    requires n > 0
    ensures  n < exp(2, log2(n)+1)
  {
    if n == 1 {
      // BC: n = 1
      calc {
           1; 
        <  2; 
        == { lem_exp2FirstValues(); }
           exp(2, 1);
        == { lem_log2FirstValues(); }
           exp(2, log2(1)+1);   
      }
    } else {
      // Step. n > 1
      //   IH: n/2 < 2^(log2(n/2)+1)
      //    T:   n < 2^(log2(n)+1)
      calc {
           exp(2, log2(n)+1);
        == { reveal exp(); }
           2*exp(2, log2(n));
        == { reveal log2(); }
           2*exp(2, log2(n/2)+1);
        >  { lem_log2exp2_bounds(n/2); 
             assert n < 2*exp(2, log2(n/2)+1); }
           n;
      }
    }
  }

  // n>0 ==> log2(n+1) <= n
  lemma lem_log2nPlus1LEQn(n:nat) 
    requires n > 0 
    ensures  log2(n+1) <= n
    decreases n
  {
    if n == 1 {   
      // BC: n = 1
      calc {
           log2(2);
        == { lem_log2FirstValues(); }
           1;   
        <= 1;   
      }
    } else {  
      // Step. n > 1
      //   IH: log2(n)   <= n-1
      //    T: log2(n+1) <= n
      calc {  
           log2(n+1);
        == { reveal log2(); }
           1 + log2((n+1)/2);
        <= { assert (n+1)/2 <= n; lem_log2Mono((n+1)/2, n); } 
           1 + log2(n);   
        <= { lem_log2nPlus1LEQn(n-1); }  // by IH 
           1 + (n-1);
        == n;           
      }
    }
  }

  // n>=4 ==> log2(n) <= n-2
  lemma lem_log2nLEQnMinus2(n:nat)
    requires n >= 4 
    ensures  log2(n) <= n-2
    decreases n
  {
    if n == 4 {   
      // BC: n = 4
      calc {
           log2(4);
        == { lem_log2FirstValues(); }
           2;   
        <= 2;
        == 4-2;   
      }
    } else {  
      // Step. n > 4
      //   IH: log2(n-1) <= n-3
      //    T: log2(n)   <= n-2
      calc {  
           log2(n);
        == { reveal log2(); }
           1 + log2(n/2);
        <= { assert n/2 <= n-1; lem_log2Mono(n/2, n-1); } 
           1 + log2(n-1);   
        <= { lem_log2nPlus1LEQn(n-1); }  // by IH 
           1 + (n-3);
        == n-2;           
      }
    }
  }

  // n>0 ==> log2(n) <= n-1
  lemma lem_log2nLEQnMinus1(n:nat)  
    requires n > 0 
    ensures  log2(n) <= n-1
    decreases n
  {
    lem_log2nPlus1LEQn(n);
    assert log2(n+1) <= n;
    assert log2((n+1)-1) <= ((n+1))-2 by { reveal log2(); }
    assert log2(n) <= n-1;
  }

  // n <= n^2
  lemma lem_nLQexpn2(n:nat)
    ensures n <= exp(n,2)
    decreases n
  {
    if n == 0 {
      assert 0 <= exp(0,2);
    } else {
      calc {  
           n <= exp(n,2);
        == 0 <= exp(n,2) - n;
        == { reveal exp(); }
           0 <= n*exp(n,2) - n;  
        == 0 <= n*(exp(n,2) - 1);  
        == 0 <= exp(n,2) - 1;      
        == 1 <= exp(n,2);
        == { lem_expIsPositive(n,2); }
           true;                     
      }
    }
  }

  // n < 2^n
  lemma lem_nLQexp2n(n:nat)
    ensures n < exp(2,n)
    decreases n 
  {
    if n == 0 {   
      // BC: n = 0
      calc {
           0;
        <  1;
        == { reveal exp(); }
           exp(2,n);     
      }
    } else {  
      // Step. n > 0
      //   IH: n-1 < 2^(n-1)
      //    T: n   < 2^n
      calc {  
           n;
        == (n-1) + 1;
        <  { lem_nLQexp2n(n-1); }   // by IH 
           exp(2,n-1) + 1;
        <= { assert exp(2,n-1) >= 1; }
           exp(2,n-1) + exp(2,n-1);
        == { reveal exp(); }
           exp(2,n);       
      }
    }
  }

  // n>=4 ==> n <= 2^(n-2)
  lemma {:axiom} lem_nLEQexp2nMinus2(n:nat)
    requires n >= 4
    ensures  n <= exp(2,n-2)
    decreases n
  {
    if n == 4 {   
      // BC: n = 4
      calc {
           4;
        <= 4;
        == { reveal exp(); }
           exp(2,2);     
      }
    } else {  
      // Step. n > 4
      //   IH: n-1 <= 2^(n-3)
      //    T: n   <= 2^(n-2)
      calc {  
           n;
        == (n-1) + 1;
        <= { lem_nLEQexp2nMinus2(n-1); }   // by IH 
           exp(2,n-3) + 1;
        <= { lem_expIsPositive(2, n-3); assert exp(2,n-3) >= 1; }
           exp(2,n-3) + exp(2,n-3);
        == { reveal exp(); }
           exp(2,n-2);       
      }
    } 
  }

  // 4^2 <= 2^4
  lemma lem_expn2LQexp2nBC()
    ensures exp(4,2) <= exp(2,4)
  {
    reveal exp();
  }

  // n>=4 ==> n^2 < 2^n
  lemma lem_expn2LQexp2n(n:nat)
    requires n >= 4
    ensures  exp(n,2) <= exp(2,n)
    decreases n
  {
    if n == 4 {   
      // BC: n = 4
      lem_expn2LQexp2nBC();
    } else {  
      // Step. n > 4
      //   IH: (n-1)^2 <= 2^{n-1}
      //    T: n^2 <= 2^n
      calc {   
           exp(n,2);
        == { lem_binomial(n); }
           exp(n-1,2) + 2*(n-1) + 1;
        <= { lem_expn2LQexp2n(n-1);  }   // by IH  
           exp(2,n-1) + 2*(n-1) + 1; 
        <= { lem_nLEQexp2nMinus2(n); reveal exp(); assert 2*n <= exp(2,n-1); }  
           2*exp(2,n-1);
        == { reveal exp(); }
           exp(2,n);              
      }
    }
  }

}