
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

  lemma lem_exp2FirstValues()
    ensures exp(2,0) == 1
    ensures exp(2,1) == 2 
    ensures exp(2,2) == 4
    ensures exp(2,3) == 8
    ensures exp(2,4) == 16
  {
    reveal exp();
  }

  // b >= 1 /\ n <= m ==> b^n <= b^m
  lemma lem_expMonoIncr(b:nat, n:nat, m:nat)
    requires b >= 1
    ensures  n <= m ==> exp(b, n) <= exp(b, m)
    decreases n, m
  { 
    reveal exp();
    if n != 0 && m != 0 {  
      lem_expMonoIncr(b, n-1, m-1); 
    }
  }

  // n <= m ==> n^e <= m^e
  lemma lem_expBaseMonoIncr(e:nat, n:nat, m:nat)
    ensures n <= m ==> exp(n, e) <= exp(m, e)
    decreases n, m
  {  
    reveal exp();
    if n != 0 && m != 0 {  
      lem_expBaseMonoIncr(e, n-1, m-1);  // TODO
    }
  }  

  // b>0 ==> b^e > 0
  lemma lem_expIsPositive(b:nat, e:nat)
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
        >  { lem_expIsPositive(b, e-1); }
           0;  
      }
    }
  }
  
  // n^1 == n
  lemma lem_expn1(n:nat)
    ensures exp(n,1) == n
  { reveal exp; }

  // n^2 == n*n
  lemma lem_expn2(n:nat)
    ensures exp(n,2) == n*n
  { reveal exp; }  

  // n^3 == n*n*n
  lemma lem_expn3(n:nat)
    ensures exp(n,3) == n*n*n  
  { reveal exp; }  

  // (n+1)^2 == n*n + 2*n + 1
  lemma {:axiom} lem_binomial2(n:nat)
    ensures exp(n+1,2) == n*n + 2*n + 1

  // n^2 == (n-1)*2 + 2*(n-1) + 1
  lemma {:axiom} lem_binomial(n:nat)
    requires n > 0
    ensures exp(n,2) == exp(n-1,2) + 2*(n-1) + 1 
    
  /******************************************************************************
    Special 2^x
  ******************************************************************************/

  // 2^x
  ghost function exp2(e:nat) : nat
  { 
    exp(2, e)
  }

  /******************************************************************************
    Universal clausures of lemmas
  ******************************************************************************/

  lemma lem_expn1All()
    ensures forall n:nat :: exp(n,1) == n  
  { 
    forall n:nat ensures exp(n,1) == n {
      lem_expn1(n);
    }
  }

  lemma lem_expn2All()
    ensures forall n:nat :: exp(n,2) == n*n  
  {
    forall n:nat ensures exp(n,2) == n*n {
      lem_expn2(n);
    }
  }  

  lemma lem_expn3All()
    ensures forall n:nat :: exp(n,3) == n*n*n 
  {
    forall n:nat ensures exp(n,3) == n*n*n {
      lem_expn3(n);
    }
  }   

}