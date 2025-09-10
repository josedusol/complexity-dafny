include "./LemFunction.dfy"
//include "./Order.dfy"

/******************************************************************************
  Exponentiation over non-negative integers
******************************************************************************/

module ExpNat {

  import opened LemFunction
  //import opened Order

  // b^e
  opaque ghost function exp(b:nat, e:nat) : nat
    decreases e
  {
    if e == 0 then 1 else b*exp(b, e-1)
  }

  // b > 0 ⟹ b^e > 0
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
  
  /******************************************************************************
    Relate exp(x,0), exp(x,1), exp(x,2), etc. to Dafny primitive powers
  ******************************************************************************/

  // n^0 = 1
  lemma lem_exp_Pow0(n:nat)
    ensures exp(n,0) == 1
  { 
    reveal exp;
  }

  lemma lem_exp_Pow0Auto()
    ensures forall n:nat :: exp(n,0) == 1  
  { 
    forall n:nat ensures exp(n,0) == 1 {
      lem_exp_Pow0(n);
    }
  }

  // n^1 = n
  lemma lem_exp_Pow1(n:nat)
    ensures exp(n,1) == n
  { 
    reveal exp;
  }

  lemma lem_exp_Pow1Auto()
    ensures forall n:nat :: exp(n,1) == n  
  { 
    forall n:nat ensures exp(n,1) == n {
      lem_exp_Pow1(n);
    }
  }

  // n^2 = n*n
  lemma lem_exp_Pow2(n:nat)
    ensures exp(n,2) == n*n
  { 
    reveal exp; 
  }  

  lemma lem_exp_Pow2Auto()
    ensures forall n:nat :: exp(n,2) == n*n  
  {
    forall n:nat ensures exp(n,2) == n*n {
      lem_exp_Pow2(n);
    }
  } 

  // n^3 = n*n*n
  lemma lem_exp_Pow3(n:nat)
    ensures exp(n,3) == n*n*n  
  { reveal exp; }  

  lemma lem_exp_Pow3Auto()
    ensures forall n:nat :: exp(n,3) == n*n*n 
  {
    forall n:nat ensures exp(n,3) == n*n*n {
      lem_exp_Pow3(n);
    }
  } 

  /******************************************************************************
    Order properties on the exponent with base >= 1 (or > 1)
  ******************************************************************************/

  // b > 1 ∧ n < m ⟹ b^n < b^m
  lemma lem_exp_StrictIncr(b:nat, n:nat, m:nat)
    requires b > 1
    ensures  n < m ==> exp(b, n) < exp(b, m)
    decreases n, m
  { 
    reveal exp();
    if n != 0 && m != 0 {  
      lem_exp_StrictIncr(b, n-1, m-1); 
    }
  }

  lemma lem_exp_StrictIncrAuto()
    ensures forall b:nat, n:nat, m:nat :: 
      b > 1 && n < m ==> exp(b, n) < exp(b, m)
  {
    forall b:nat, n:nat, m:nat | b > 1
      ensures n < m ==> exp(b, n) < exp(b, m)
    {
      lem_exp_StrictIncr(b, n, m);
    }       
  }

  // Previous fact is reversible
  // b > 1 ∧ b^n < b^m ⟹ n < m
  lemma lem_exp_StrictIncrRev(b:nat, n:nat, m:nat)
    requires b > 1
    ensures  exp(b, n) < exp(b, m) ==> n < m
  { 
    var exp_b:nat->nat := x => exp(b, x);
    assert forall x,y :: x < y ==> exp_b(x) < exp_b(y)
      by { lem_exp_StrictIncrAuto(); }
    lem_fun_StrictIncrIMPinjectiveNat(exp_b);
    assert forall x,y :: exp_b(x) < exp_b(y) ==> x < y;
    assert forall x :: exp_b(x) == exp(b, x);
  }

  lemma lem_exp_StrictIncrRevAuto()
    ensures forall b:nat, n:nat, m:nat :: 
      b > 1 && exp(b, n) < exp(b, m) ==> n < m
  {
    forall b:nat, n:nat, m:nat | b > 1
      ensures exp(b, n) < exp(b, m) ==> n < m
    {
      lem_exp_StrictIncrRev(b, n, m);
    }       
  }  

  // Join previous facts into an equivalence
  // b > 1 ⟹ (x < y ⟺ b^x < b^y)
  lemma lem_exp_StrictIncrIFF(b:nat, n:nat, m:nat)
    requires b > 1
    ensures  n < m <==> exp(b, n) < exp(b, m)
  { 
    lem_exp_StrictIncr(b,n,m);
    lem_exp_StrictIncrRev(b,n,m);
  }

  lemma lem_exp_StrictIncrIFFAuto()
    ensures forall b:nat, n:nat, m:nat :: 
      b > 1 ==> (n < m <==> exp(b, n) < exp(b, m))
  {
    forall b:nat, n:nat, m:nat | b > 1
      ensures n < m <==> exp(b, n) < exp(b, m)
    {
      lem_exp_StrictIncrIFF(b, n, m);
    }       
  }    

  // Weak version of lem_exp_StrictIncrIFF
  // b > 1 ⟹ (x <= y ⟺ b^x <= b^y)
  lemma lem_exp_MonoIncrIFF(b:nat, n:nat, m:nat)
    requires b > 1
    ensures  n <= m <==> exp(b, n) <= exp(b, m)
  {
    lem_exp_StrictIncrIFFAuto();
  }

  lemma lem_exp_MonoIncrIFFAuto()
    ensures forall b:nat, n:nat, m:nat :: 
      b > 1 ==> (n <= m <==> exp(b, n) <= exp(b, m))
  {
    forall b:nat, n:nat, m:nat | b > 1
      ensures n <= m <==> exp(b, n) <= exp(b, m)
    {
      lem_exp_MonoIncrIFF(b, n, m);
    }       
  }  

  // Weak version of lem_exp_StrictIncr, but also holds when b=1
  // b >= 1 ∧ n <= m ⟹ b^n <= b^m
  lemma lem_exp_MonoIncr(b:nat, n:nat, m:nat)
    requires b >= 1
    ensures  n <= m ==> exp(b, n) <= exp(b, m)
    decreases n, m
  { 
    if b == 1 {
      reveal exp();
    } else if b > 1 {
      lem_exp_StrictIncr(b, n, m);
    }    
  }

  /******************************************************************************
    Order properties on the base
  ******************************************************************************/
  
  
  // n <= m ⟹ n^e <= m^e
  lemma {:axiom} lem_exp_BaseMonoIncr(e:nat, n:nat, m:nat)
    ensures n <= m ==> exp(n, e) <= exp(m, e)
    decreases n, m
  // {   // TODO
  //   reveal exp();
  //   if n != 0 && m != 0 {  
  //     lem_exp_BaseMonoIncr(e, n-1, m-1); 
  //   }
  // }  

  /******************************************************************************
    Binomial expansion
  ******************************************************************************/

  // (n+1)^2 = n*n + 2*n + 1
  lemma {:axiom} lem_exp_binomial(n:nat)
    ensures exp(n+1,2) == n*n + 2*n + 1

  // n^2 = (n-1)*2 + 2*(n-1) + 1
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

}