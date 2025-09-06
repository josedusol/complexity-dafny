
/******************************************************************************
  Exponentiation over non-negative integers
******************************************************************************/

module ExpNat {

  // b^e
  opaque ghost function exp(b:nat, e:nat) : nat
    decreases e
  {
    if e == 0 then 1 else b*exp(b, e-1)
  }

  // b >= 1 /\ n <= m ==> b^n <= b^m
  lemma lem_exp_MonoIncr(b:nat, n:nat, m:nat)
    requires b >= 1
    ensures  n <= m ==> exp(b, n) <= exp(b, m)
    decreases n, m
  { 
    reveal exp();
    if n != 0 && m != 0 {  
      lem_exp_MonoIncr(b, n-1, m-1); 
    }
  }

  // n <= m ==> n^e <= m^e
  lemma {:axiom} lem_exp_BaseMonoIncr(e:nat, n:nat, m:nat)
    ensures n <= m ==> exp(n, e) <= exp(m, e)
    decreases n, m
  // {   // TODO
  //   reveal exp();
  //   if n != 0 && m != 0 {  
  //     lem_exp_BaseMonoIncr(e, n-1, m-1); 
  //   }
  // }  

  // b>0 ==> b^e > 0
  lemma lem_exp_Positive(b:nat, e:nat)
    requires b > 0
    ensures exp(b,e) > 0
  {
    if e == 0 { 
      // BC: e = 0
      calc {
           exp(b, 0);
        == { reveal exp(); }
           1;
        >  0;  
      }
    } else {
      // Step. e > 0
      //   IH: b^(e-1)  > 0
      //    T:      b^e > 0
      calc {
           exp(b,e);
        == { reveal exp(); }
           b*exp(b, e-1);
        >  { lem_exp_Positive(b, e-1); }
           0;  
      }
    }
  }
  
  // n^1 == n
  lemma lem_exp_n1(n:nat)
    ensures exp(n,1) == n
  { reveal exp; }

  // n^2 == n*n
  lemma lem_exp_n2(n:nat)
    ensures exp(n,2) == n*n
  { reveal exp; }  

  // n^3 == n*n*n
  lemma lem_exp_n3(n:nat)
    ensures exp(n,3) == n*n*n  
  { reveal exp; }  

  // (n+1)^2 == n*n + 2*n + 1
  lemma {:axiom} lem_exp_binomial(n:nat)
    ensures exp(n+1,2) == n*n + 2*n + 1

  // n^2 == (n-1)*2 + 2*(n-1) + 1
  lemma {:axiom} lem_exp_binomial2(n:nat)
    requires n > 0
    ensures exp(n,2) == exp(n-1,2) + 2*(n-1) + 1 
    
  /******************************************************************************
    Special 2^x
  ******************************************************************************/

  // 2^x
  ghost function exp2(n:nat) : nat
  { 
    exp(2, n)
  }

  lemma lem_exp2_FirstValues()
    ensures exp2(0) == exp(2,0) == 1
    ensures exp2(1) == exp(2,1) == 2 
    ensures exp2(2) == exp(2,2) == 4
    ensures exp2(3) == exp(2,3) == 8
    ensures exp2(4) == exp(2,4) == 16
  {
    reveal exp();
  }  

  /******************************************************************************
    Universal clausures of lemmas
  ******************************************************************************/

  lemma lem_exp_n1Auto()
    ensures forall n:nat :: exp(n,1) == n  
  { 
    forall n:nat ensures exp(n,1) == n {
      lem_exp_n1(n);
    }
  }

  lemma lem_exp_n2Auto()
    ensures forall n:nat :: exp(n,2) == n*n  
  {
    forall n:nat ensures exp(n,2) == n*n {
      lem_exp_n2(n);
    }
  }  

  lemma lem_exp_n3Auto()
    ensures forall n:nat :: exp(n,3) == n*n*n 
  {
    forall n:nat ensures exp(n,3) == n*n*n {
      lem_exp_n3(n);
    }
  }   

}