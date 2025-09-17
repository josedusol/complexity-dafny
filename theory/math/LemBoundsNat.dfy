include "./ExpNat.dfy"
include "./Log2Nat.dfy"

/******************************************************************************
  Bounds of mathematical functions over non-negative integers
******************************************************************************/

module LemBoundsNat {

  import Exp = ExpNat
  import L2  = Log2Nat

  // n > 0 ⟹ 2^log2(n) <= n
  lemma {:induction false} lem_log2exp2_bounds(n:nat)
    requires n > 0
    ensures  Exp.exp(2, L2.log2(n)) <= n
    decreases n
  {
    if n == 1 {
      // BC: n = 1
      calc {
           Exp.exp(2, L2.log2(1));
        == { L2.lem_FirstValues(); }
           Exp.exp(2, 0);
        == { Exp.lem_Exp2FirstValues(); }
           1;   
      }
    } else {
      // Step. n > 1
      //   IH: 2^log2(n/2) <= n/2
      //    T:   2^log2(n) <= n
      assert L2.log2(n) >= 1 by { reveal L2.log2(); }
      // Note that by the definition
      assert A: L2.log2(n)-1 <= L2.log2(n/2) by { reveal L2.log2(); }
      calc {
           Exp.exp(2, L2.log2(n));
        == { reveal Exp.exp(); }
           2*Exp.exp(2, L2.log2(n)-1);
        <= { reveal A; Exp.lem_MonoIncr(2, L2.log2(n)-1, L2.log2(n/2)); }
           2*Exp.exp(2, L2.log2(n/2));
        <= { lem_log2exp2_bounds(n/2); }
           2*(n/2);
        <= n;
      }
    }
  }

  // n > 0 ⟹ n < 2^(log2(n)+1)
  lemma {:induction false} lem_nLQexp2log2nPlus1(n:nat)
    requires n > 0
    ensures  n < Exp.exp(2, L2.log2(n)+1) 
    decreases n
  {
    if n == 1 {
      // BC: n = 1
      calc {
           1; 
        <  2; 
        == { Exp.lem_Exp2FirstValues(); }
           Exp.exp(2, 1);
        == { L2.lem_FirstValues(); }
           Exp.exp(2, L2.log2(1)+1);   
      }
    } else {
      // Step. n > 1
      //   IH: n/2 < 2^(log2(n/2)+1)
      //    T:   n < 2^(log2(n)+1)
      calc {
           Exp.exp(2, L2.log2(n)+1);
        == { reveal Exp.exp(); }
           2*Exp.exp(2, L2.log2(n));
        == { reveal L2.log2(); }
           2*Exp.exp(2, L2.log2(n/2)+1);
        >  { lem_nLQexp2log2nPlus1(n/2); }  // assert n < 2*exp(2, log2(n/2)+1);
           n;
      }
    }
  }

  // n > 0 ⟹ log2(n+1) <= n
  lemma {:induction false} lem_log2nPlus1LEQn(n:nat) 
    requires n > 0 
    ensures  L2.log2(n+1) <= n
    decreases n
  {
    if n == 1 {   
      // BC: n = 1
      calc {
           L2.log2(2);
        == { L2.lem_FirstValues(); }
           1;   
        <= 1;   
      }
    } else {  
      // Step. n > 1
      //   IH: log2(n)   <= n-1
      //    T: log2(n+1) <= n
      calc {  
           L2.log2(n+1);
        == { reveal L2.log2(); }
           1 + L2.log2((n+1)/2);
        <= { assert (n+1)/2 <= n; L2.lem_MonoIncr((n+1)/2, n); } 
           1 + L2.log2(n);   
        <= { lem_log2nPlus1LEQn(n-1); }  // by IH 
           1 + (n-1);
        == n;           
      }
    }
  }

  // n >= 4 ⟹ log2(n) <= n-2
  lemma {:induction false} lem_log2nLEQnMinus2(n:nat)
    requires n >= 4 
    ensures  L2.log2(n) <= n-2
    decreases n
  {
    if n == 4 {   
      // BC: n = 4
      calc {
           L2.log2(4);
        == { L2.lem_FirstValues(); }
           2;   
        <= 2;
        == 4-2;   
      }
    } else {  
      // Step. n > 4
      //   IH: log2(n-1) <= n-3
      //    T: log2(n)   <= n-2
      calc {  
           L2.log2(n);
        == { reveal L2.log2(); }
           1 + L2.log2(n/2);
        <= { assert n/2 <= n-1; L2.lem_MonoIncr(n/2, n-1); } 
           1 + L2.log2(n-1);   
        <= { lem_log2nLEQnMinus2(n-1); }  // by IH 
           1 + (n-3);
        == n-2;           
      }
    }
  }

  // n > 0 ⟹ log2(n) <= n-1
  lemma lem_log2nLEQnMinus1(n:nat)  
    requires n > 0 
    ensures  L2.log2(n) <= n-1
    decreases n
  {
    lem_log2nPlus1LEQn(n);
    assert L2.log2(n+1) <= n;
    assert L2.log2((n+1)-1) <= ((n+1))-2 by { reveal L2.log2(); }
    assert L2.log2(n) <= n-1;
  }

  // n <= n^2
  lemma lem_nLQexpn2(n:nat)
    ensures n <= Exp.exp(n, 2)
    decreases n
  {
    if n == 0 {
      assert 0 <= Exp.exp(0,2);
    } else {
      calc {  
           n <= Exp.exp(n,2);
        == 0 <= Exp.exp(n,2) - n;
        == { reveal Exp.exp(); }
           0 <= n*Exp.exp(n,2) - n;  
        == 0 <= n*(Exp.exp(n,2) - 1);  
        == 0 <= Exp.exp(n,2) - 1;      
        == 1 <= Exp.exp(n,2);
        == { Exp.lem_Positive(n,2); }
           true;                     
      }
    }
  }

  // n < 2^n
  lemma {:induction false} lem_nLQexp2n(n:nat)
    ensures n < Exp.exp(2,n)
    decreases n 
  {
    if n == 0 {   
      // BC: n = 0
      calc {
           0;
        <  1;
        == { reveal Exp.exp(); }
           Exp.exp(2,n);     
      }
    } else {  
      // Step. n > 0
      //   IH: n-1 < 2^(n-1)
      //    T: n   < 2^n
      calc {  
           n;
        == (n-1) + 1;
        <  { lem_nLQexp2n(n-1); }   // by IH 
           Exp.exp(2,n-1) + 1;
        <= { Exp.lem_GEQone(2, n-1); assert Exp.exp(2,n-1) >= 1; }
           Exp.exp(2,n-1) + Exp.exp(2,n-1);
        == { reveal Exp.exp(); }
           Exp.exp(2,n);       
      }
    }
  }

  // n >= 4 ⟹ n <= 2^(n-2)
  lemma {:induction false} lem_nLEQexp2nMinus2(n:nat)
    requires n >= 4
    ensures  n <= Exp.exp(2,n-2)
    decreases n
  {
    if n == 4 {   
      // BC: n = 4
      calc {
           4;
        <= 4;
        == { reveal Exp.exp(); }
           Exp.exp(2,2);     
      }
    } else {  
      // Step. n > 4
      //   IH: n-1 <= 2^(n-3)
      //    T: n   <= 2^(n-2)
      calc {  
           n;
        == (n-1) + 1;
        <= { lem_nLEQexp2nMinus2(n-1); }   // by IH 
           Exp.exp(2,n-3) + 1;
        <= { Exp.lem_Positive(2, n-3); assert Exp.exp(2,n-3) >= 1; }
           Exp.exp(2,n-3) + Exp.exp(2,n-3);
        == { reveal Exp.exp(); }
           Exp.exp(2,n-2);       
      }
    } 
  }

  // 4^2 <= 2^4
  lemma lem_expn2LEQexp2nBC()
    ensures Exp.exp(4,2) <= Exp.exp(2,4)
  {
    reveal Exp.exp();
  }

  // n >= 4 ⟹ n^2 <= 2^n
  lemma {:induction false} lem_expn2LEQexp2n(n:nat) 
    requires n >= 4
    ensures  Exp.exp(n,2) <= Exp.exp(2,n)
    decreases n
  {
    if n == 4 {   
      // BC: n = 4
      lem_expn2LEQexp2nBC();
    } else {  
      // Step. n > 4
      //   IH: (n-1)^2 <= 2^{n-1}
      //    T:     n^2 <= 2^n
      calc {   
           Exp.exp(n,2);
        == { Exp.lem_Binomial2(n); }
           Exp.exp(n-1,2) + 2*(n-1) + 1;
        <= { lem_expn2LEQexp2n(n-1);  }   // by IH  
           Exp.exp(2,n-1) + 2*(n-1) + 1; 
        <= { lem_nLEQexp2nMinus2(n); reveal Exp.exp(); assert 2*n <= Exp.exp(2,n-1); }  
           2*Exp.exp(2,n-1);
        == { reveal Exp.exp(); }
           Exp.exp(2,n);              
      }
    }
  }

}