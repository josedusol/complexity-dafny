
include "./math.dfy"

/**************************************************************************
  Bounds of mathematical functions over non-negative integers
**************************************************************************/

// n > 0 ==> 2^log2(n) <= n
lemma lem_log2Pow2_bounds(n: nat)
  requires n > 0
  ensures  pow(2, log2(n)) <= n
{
  if n == 1 {
    // BC: n = 1
    calc {
         pow(2, log2(1));
      == { lem_log2FirstValues(); }
         pow(2, 0);
      == { lem_pow2FirstValues(); }
         1;   
    }
  } else {
    // Step. n > 1
    //   IH: 2^log2(n/2) <= n/2
    //    T:   2^log2(n) <= n
    assert log2(n) >= 1 by { reveal log2(); }
    // note by the definition that
    assert A: log2(n)-1 <= log2(n/2) by { reveal log2(); }
    calc {
         pow(2, log2(n));
      == { reveal pow(); }
         2*pow(2, log2(n)-1);
      <= { reveal A; lem_powMono(2, log2(n)-1, log2(n/2)); }
         2*pow(2, log2(n/2));
      <= { lem_log2Pow2_bounds(n/2); }
         2*(n/2);
      <= n;
    }
  }
}

// n > 0 ==> n < 2^(log2(n)+1)
lemma lem_nLQPow2log2nPlus1(n:nat)
  requires n > 0
  ensures  n < pow(2, log2(n)+1)
{
  if n == 1 {
    // BC: n = 1
    calc {
         1; 
      <  2; 
      == { lem_pow2FirstValues(); }
         pow(2, 1);
      == { lem_log2FirstValues(); }
         pow(2, log2(1)+1);   
    }
  } else {
    // Step. n > 1
    //   IH: n/2 < 2^(log2(n/2)+1)
    //    T:   n < 2^(log2(n)+1)
    calc {
         pow(2, log2(n)+1);
      == { reveal pow(); }
         2*pow(2, log2(n));
      == { reveal log2(); }
         2*pow(2, log2(n/2)+1);
      >  { lem_log2Pow2_bounds(n/2); 
           assert n < 2*pow(2, log2(n/2)+1); }
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
lemma lem_nLQpown2(n:nat)
  ensures n <= pow(n,2)
  decreases n
{
  if n == 0 {
    assert 0 <= pow(0,2);
  } else {
    calc {  
         n <= pow(n,2);
      == 0 <= pow(n,2) - n;
      == { reveal pow(); }
         0 <= n*pow(n,2) - n;  
      == 0 <= n*(pow(n,2) - 1);  
      == 0 <= pow(n,2) - 1;      
      == 1 <= pow(n,2);
      == { lem_powIsPositive(n,2); }
         true;                     
    }
  }
}

// n < 2^n
lemma lem_nLQpow2n(n:nat)
  ensures n < pow(2,n)
  decreases n 
{
  if n == 0 {   
    // BC: n = 0
    calc {
         0;
      <  1;
      == { reveal pow(); }
         pow(2,n);     
    }
  } else {  
    // Step. n > 0
    //   IH: n-1 < 2^(n-1)
    //    T: n   < 2^n
    calc {  
         n;
      == (n-1) + 1;
      <  { lem_nLQpow2n(n-1); }   // by IH 
         pow(2,n-1) + 1;
      <= { assert pow(2,n-1) >= 1; }
         pow(2,n-1) + pow(2,n-1);
      == { reveal pow(); }
         pow(2,n);       
    }
  }
}

// n>=4 ==> n <= 2^(n-2)
lemma {:axiom} lem_nLEQpow2nMinus2(n:nat)
  requires n >= 4
  ensures  n <= pow(2,n-2)
  decreases n
{
  if n == 4 {   
    // BC: n = 4
    calc {
         4;
      <= 4;
      == { reveal pow(); }
         pow(2,2);     
    }
  } else {  
    // Step. n > 4
    //   IH: n-1 <= 2^(n-3)
    //    T: n   <= 2^(n-2)
    calc {  
         n;
      == (n-1) + 1;
      <= { lem_nLEQpow2nMinus2(n-1); }   // by IH 
         pow(2,n-3) + 1;
      <= { lem_powIsPositive(2, n-3); assert pow(2,n-3) >= 1; }
         pow(2,n-3) + pow(2,n-3);
      == { reveal pow(); }
         pow(2,n-2);       
    }
  } 
}

// 4^2 <= 2^4
lemma lem_pown2LQpow2nBC()
  ensures pow(4,2) <= pow(2,4)
{
  reveal pow();
}

// n>=4 ==> n^2 < 2^n
lemma lem_pown2LQpow2n(n:nat)
  requires n >= 4
  ensures  pow(n,2) <= pow(2,n)
  decreases n
{
  if n == 4 {   
    // BC: n = 4
    lem_pown2LQpow2nBC();
  } else {  
    // Step. n > 4
    //   IH: (n-1)^2 <= 2^{n-1}
    //    T: n^2 <= 2^n
    calc {   
         pow(n,2);
      == { lem_binomial(n); }
         pow(n-1,2) + 2*(n-1) + 1; 
      <= { lem_pown2LQpow2n(n-1);  }   // by IH  
         pow(2,n-1) + 2*(n-1) + 1; 
      <= { lem_nLEQpow2nMinus2(n); reveal pow(); assert 2*n <= pow(2,n-1); }  
         2*pow(2,n-1);
      == { reveal pow(); }
         pow(2,n);              
    }
  }
}