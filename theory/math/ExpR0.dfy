include "./ExpNat.dfy"
include "./LemFunction.dfy"
include "./LemReal.dfy"
include "./TypeR0.dfy"

/******************************************************************************
  Exponentiation over non negative reals
******************************************************************************/

// This module serves as an alternative to the ExpReal module.
// To work with negative exponents it is not possible to use this definition
// of exp, instead pow(x:R0, y:real):R0 wich extends exp should be used.
// We prefer ExpReal.exp because is more easy to work with.

module ExpR0 {

  import N = ExpNat
  import opened LemFunction
  import opened LemReal
  import opened TypeR0

  // x^y
  ghost function {:axiom} exp(x:R0, y:R0) : R0

  // x > 0 ⟹ x^y > 0
  lemma {:axiom} lem_Positive(x:R0, y:R0)
    requires x > 0.0
    ensures  exp(x, y) > 0.0         

  // x > 1 ∧ y > 0 ⟹ x^y > 1
  lemma {:axiom} lem_GTone(x:R0, y:R0)
    requires x > 1.0 && y > 0.0
    ensures  exp(x, y) > 1.0     

  // x^0 = 1
  lemma {:axiom} lem_Zero(x:R0)
    ensures  exp(x, 0.0) == 1.0 

  // x^1 = x
  lemma {:axiom} lem_One(x:R0)
    ensures  exp(x, 1.0) == x

  // y > 0 ⟹ 0^y = 0
  lemma {:axiom} lem_BaseZero(y:R0)
    requires y > 0.0
    ensures  exp(0.0, y) == 0.0     

  // 1^y = 1
  lemma {:axiom} lem_BaseOne(y:R0)
    ensures  exp(1.0, y) == 1.0     

  // x^(y+z) = (x^y)*(x^z)
  lemma {:axiom} lem_Product(x:R0, y:R0, z:R0)
    ensures  exp(x, y+z) == exp(x, y)*exp(x, z)  

  // (x^y)^z = x^(y*z)
  lemma {:axiom} lem_Exp(x:R0, y:R0, z:R0)
    ensures  exp(exp(x, y), z) == exp(x, y*z) 

  // The only other axiom we take is lem_BaseStrictIncr, see below in the list
  // of order properties on the base

  /******************************************************************************
    Universal closures of the axioms
  ******************************************************************************/

  lemma lem_PositiveAuto()
    ensures forall x:real, y:real ::  
            x > 0.0 && y >= 0.0 ==> exp(x, y) > 0.0
  {
     forall x:real, y:real | x > 0.0 && y >= 0.0
      ensures exp(x, y) > 0.0
    {
      lem_Positive(x, y);
    }
  }  

  lemma lem_GToneAuto()
    ensures forall x:R0, y:R0 ::  
            x > 1.0 && y > 0.0 ==> exp(x, y) > 1.0
  {
     forall x:R0, y:R0 | x > 1.0 && y > 0.0
      ensures exp(x, y) > 1.0
    {
      lem_GTone(x, y);
    }
  } 

  lemma lem_ZeroAuto()
    ensures forall x:R0 :: x > 0.0 ==> exp(x, 0.0) == 1.0 
  {
    forall x:R0 | x > 0.0
      ensures exp(x, 0.0) == 1.0 
    {
      lem_Zero(x);
    }
  }

  lemma lem_OneAuto()
    ensures forall x:R0 :: x > 0.0 ==> exp(x, 1.0) == x 
  {
    forall x:R0 | x > 0.0
      ensures exp(x, 1.0) == x 
    {
      lem_One(x);
    }    
  }

  lemma lem_BaseZeroAuto()
    ensures forall y:R0 :: y > 0.0 ==> exp(0.0, y) == 0.0 
  {
    forall y:R0 | y > 0.0
      ensures exp(0.0, y) == 0.0 
    {
      lem_BaseZero(y);
    }
  }

  lemma lem_BaseOneAuto()
    ensures forall y:R0 :: exp(1.0, y) == 1.0 
  {
    forall y:R0
      ensures exp(1.0, y) == 1.0 
    {
      lem_BaseOne(y);
    }
  }

  lemma lem_ProductAuto()
    ensures forall x:R0, y:R0, z:R0 :: 
      exp(x, y+z) == exp(x, y)*exp(x, z)
  {
    forall x:R0, y:R0, z:R0
      ensures exp(x, y+z) == exp(x, y)*exp(x, z)
    {
      lem_Product(x, y, z);
    }   
  }

  lemma lem_ExpAuto()
    ensures forall x:R0, y:R0, z:R0 :: 
            x >= 0.0 ==> exp(exp(x, y), z) == exp(x, y*z) 
  {
    forall x:R0, y:R0, z:R0 | x >= 0.0
      ensures exp(exp(x, y), z) == exp(x, y*z) 
    {
      lem_Exp(x, y, z);
    }   
  }

  /******************************************************************************
    Derived properties
  ******************************************************************************/

  // x >= 1 ⟹ x^y >= 1
  lemma {:axiom} lem_GEQone(x:R0, y:R0)
    requires x >= 1.0
    ensures  exp(x, y) >= 1.0  

  lemma lem_GEQoneAuto()
    ensures forall x:real, y:real :: 
      x >= 1.0 && y >= 0.0 ==> exp(x, y) >= 1.0  
  {
    forall x:real, y:real | x >= 1.0 && y >= 0.0
      ensures exp(x, y) >= 1.0  
    {
      lem_GEQone(x, y);
    }
  }

  // x*(x^y) = x^(y+1)
  lemma lem_Def(x:R0, y:R0)
    ensures x*exp(x, y) == exp(x, y + 1.0)
  { 
    calc {
          x*exp(x, y);
      == { lem_One(x); }
          exp(x, 1.0)*exp(x, y);
      == { lem_Product(x, 1.0, y); }
          exp(x, y + 1.0);
    } 
  } 

  lemma lem_DefAuto()
    ensures forall x:R0, y:R0 :: 
      x*exp(x, y) == exp(x, y + 1.0)
  {
    forall x:R0, y:R0
      ensures x*exp(x, y) == exp(x, y + 1.0)
    {
      lem_Def(x, y);
    }
  }

  /******************************************************************************
    Relate exp(x,0), exp(x,1), exp(x,2), etc. to Dafny primitive powers
  ******************************************************************************/

  // x^0 = 1
  lemma lem_Pow0(x:R0) 
    ensures exp(x, 0.0) == 1.0
  { 
    lem_Zero(x);
  }

  lemma lem_Pow0Auto()
    ensures forall x:R0 :: exp(x, 0.0) == 1.0
  {
    forall x:R0 ensures exp(x, 0.0) == 1.0
    {
      lem_Pow0(x);
    }
  }

  // x^1 = x
  lemma lem_Pow1(x:R0) 
    ensures exp(x, 1.0) == x
  { 
    lem_One(x);
  }

  lemma lem_Pow1Auto()
    ensures forall x:R0 :: exp(x, 1.0) == x
  {
    forall x:R0 ensures exp(x, 1.0) == x
    {
      lem_Pow1(x);
    }
  }

  // x^2 = x*x
  lemma lem_Pow2(x:R0) 
    ensures exp(x, 2.0) == x*x
  {  
    if x == 0.0 {
      lem_BaseZero(2.0);
    } else {
      calc {
          exp(x, 2.0);
        == { lem_Product(x, 1.0, 1.0); }
          exp(x, 1.0)*exp(x, 1.0);
        == { lem_One(x); }
          x*x;
      } 
    }
  } 

  lemma lem_Pow2Auto()
    ensures forall x:R0 :: exp(x, 2.0) == x*x
  {
    forall x:R0 ensures exp(x, 2.0) == x*x
    {
      lem_Pow2(x);
    }
  }

  // x^3 = x*x*x
  lemma lem_Pow3(x:R0) 
    ensures exp(x, 3.0) == x*x*x
  {  
    calc {
         exp(x, 3.0);
      == { lem_Product(x, 1.0, 2.0); }
         exp(x, 1.0)*exp(x, 2.0);
      == { lem_Product(x, 1.0, 1.0); }
         exp(x, 1.0)*(exp(x, 1.0)*exp(x, 1.0));
      == { lem_One(x); }
         x*(x*x);
      == x*x*x; 
    } 
  }    

  lemma lem_Pow3Auto()
    ensures forall x:R0 :: exp(x, 3.0) == x*x*x
  {
    forall x:R0 ensures exp(x, 3.0) == x*x*x
    {
      lem_Pow3(x);
    }
  }

  /******************************************************************************
    Extend exp for negative exponents
  ******************************************************************************/

  ghost function pow(x:R0, y:real): R0
    requires x > 0.0
  {
    if y >= 0.0 
    then exp(x, y) 
    else lem_Positive(x, -y); 1.0 / exp(x, -y)
  }

  /******************************************************************************
    Order properties on the exponent with base >= 1 (or > 1)
  ******************************************************************************/

  // Strict increasing
  // b > 1 ∧ x < y ⟹ b^x < b^y
  lemma {:axiom} lem_StrictIncr(b:R0, x:R0, y:R0)
    requires b > 1.0
    ensures  x < y ==> exp(b, x) < exp(b, y)
  {
    if x < y {
      var d :| d > 0.0 && y == x + d
        by { lem_PositiveDifference(x, y); }
      assert A: exp(b, x) > 0.0 by { lem_Positive(b, x);}
      calc {
           exp(b, y);
        == { lem_Product(b, x, d); }
           exp(b, x) * exp(b, d);
        >  { assert d > 0.0; lem_GTone(b, d); reveal A; }
           exp(b, x) * 1.0;
        == exp(b, x);       
      }
    }
  }

  lemma lem_StrictIncrAuto()
    ensures forall b:R0, x:R0, y:R0 :: 
      b > 1.0 && x < y ==> exp(b, x) < exp(b, y)
  {
    forall b:R0, x:R0, y:R0 | b > 1.0
      ensures x < y ==> exp(b, x) < exp(b, y)
    {
      lem_StrictIncr(b, x, y);
    }       
  }

  // Previous fact is reversible
  // b > 1 ∧ b^x < b^y ⟹ x < y
  lemma lem_StrictIncrREV(b:R0, x:R0, y:R0)
    requires b > 1.0
    ensures  exp(b, x) < exp(b, y) ==> x < y
  { 
    var exp_b:real->real := (x => if x >= 0.0 then exp(b, x) else 0.0);
    assert forall x,y :: x >= 0.0 && x >= 0.0 && x < y ==> exp_b(x) < exp_b(y)
      by { lem_StrictIncrAuto(); }
    lem_StrictIncrImpInjectiveRealPred(exp_b, x => x >= 0.0);
    assert forall x,y :: x >= 0.0 && x >= 0.0 && exp_b(x) < exp_b(y) ==> x < y;
    assert forall x :: x >= 0.0 ==> exp_b(x) == exp(b, x);
  }

  lemma lem_StrictIncrREVAuto()
    ensures forall b:R0, x:R0, y:R0 :: 
      b > 1.0 && exp(b, x) < exp(b, y) ==> x < y
  {
    forall b:R0, x:R0, y:R0 | b > 1.0
      ensures exp(b, x) < exp(b, y) ==> x < y
    {
      lem_StrictIncrREV(b, x, y);
    }       
  }  

  // Join previous facts into an equivalence
  // b > 1 ⟹ (x < y ⟺ b^x < b^y)
  lemma lem_StrictIncrIFF(b:R0, x:R0, y:R0)
    requires b > 1.0
    ensures  x < y <==> exp(b, x) < exp(b, y)
  { 
    lem_StrictIncr(b,x,y);
    lem_StrictIncrREV(b,x,y);
  }

  lemma lem_StrictIncrIFFAuto()
    ensures forall b:R0, x:R0, y:R0 :: 
      b > 1.0 ==> (x < y <==> exp(b, x) < exp(b, y))
  {
    forall b:R0, x:R0, y:R0 | b > 1.0
      ensures x < y <==> exp(b, x) < exp(b, y)
    {
      lem_StrictIncrIFF(b, x, y);
    }       
  }    

  // Weak version of lem_StrictIncrIFF
  // b > 1 ⟹ (x <= y ⟺ b^x <= b^y)
  lemma lem_MonoIncrIFF(b:R0, x:R0, y:R0)
    requires b > 1.0
    ensures  x <= y <==> exp(b, x) <= exp(b, y)
  {
    lem_StrictIncrIFFAuto();
  }

  lemma lem_MonoIncrIFFAuto()
    ensures forall b:R0, x:R0, y:R0 :: 
      b > 1.0 ==> (x <= y <==> exp(b, x) <= exp(b, y))
  {
    forall b:R0, x:R0, y:R0 | b > 1.0
      ensures x <= y <==> exp(b, x) <= exp(b, y)
    {
      lem_MonoIncrIFF(b, x, y);
    }       
  }  

  // Weak version of lem_StrictIncr, but also holds when x=1
  // b >= 1 ∧ x <= y ⟹ b^x <= b^y
  lemma lem_MonoIncr(b:R0, x:R0, y:R0)
    requires b >= 1.0
    ensures  x <= y ==> exp(b, x) <= exp(b, y)
  {
    if b == 1.0 {
      lem_BaseOne(x);
      lem_BaseOne(y);
    } else if b > 1.0 {
      lem_StrictIncr(b, x, y);
    }    
  }

  /******************************************************************************
    Order properties on the exponent with base 0 < b < 1
  ******************************************************************************/

  // Strictly decreasing
  // 0 < b < 1 ∧ x < y ⟹ b^x > b^y   
  lemma {:axiom} lem_StrictDecr(b:R0, x:R0, y:R0)
    requires 0.0 < b < 1.0
    ensures x < y ==> exp(b, x) > exp(b, y) 

  lemma lem_StrictDecrAuto()
    ensures forall b:R0, x:R0, y:R0 :: 
      0.0 < b < 1.0 && x < y ==> exp(b, x) > exp(b, y)
  {
    forall b:R0, x:R0, y:R0 | 0.0 < b < 1.0
      ensures x < y ==> exp(b, x) > exp(b, y)
    {
      lem_StrictDecr(b, x, y);
    }       
  }

  // Previous fact is reversible
  // 0 < b < 1 ∧ b^x > b^y ⟹ x < y
  lemma lem_StrictDecrREV(b:R0, x:R0, y:R0)
    requires 0.0 < b < 1.0
    ensures exp(b, x) > exp(b, y) ==> x < y
  {
    var exp_b:real->real := (x => if x >= 0.0 then exp(b, x) else 0.0);
    assert forall x,y :: x >= 0.0 && y >= 0.0 ==> (x < y ==> exp_b(x) > exp_b(y))
      by { lem_StrictDecrAuto(); }
    lem_StrictDecrImpInjectiveRealPred(exp_b, x => x >= 0.0);
    assert forall x,y :: x >= 0.0 && y >= 0.0 ==> (exp_b(x) > exp_b(y) ==> x < y);
    assert forall x :: x >= 0.0 ==> exp_b(x) == exp(b, x);       
  }   

  lemma lem_StrictDecrREVAuto()
    ensures forall b:R0, x:R0, y:R0 :: 
      0.0 < b < 1.0 && exp(b, x) > exp(b, y) ==> x < y
  {
    forall b:R0, x:R0, y:R0 | 0.0 < b < 1.0
      ensures exp(b, x) > exp(b, y) ==> x < y
    {
      lem_StrictDecrREV(b, x, y);
    }             
  }  

  // Join previous facts into an equivalence
  // 0 < b < 1 ⟹ (x < y ⟺ b^x > b^y)  
  lemma lem_StrictDecrIFF(b:R0, x:R0, y:R0)
    requires 0.0 < b < 1.0
    ensures x < y <==> exp(b, x) > exp(b, y)
  {
    lem_StrictDecr(b, x, y);
    lem_StrictDecrREV(b, x, y);
  }

  lemma lem_StrictDecrIFFAuto()
    ensures forall b:R0, x:R0, y:R0 :: 
      0.0 < b < 1.0 ==> (x < y <==> exp(b, x) > exp(b, y))
  {
    forall b:R0, x:R0, y:R0 | 0.0 < b < 1.0
      ensures x < y <==> exp(b, x) > exp(b, y)
    {
      lem_StrictDecrIFF(b, x, y);
    }             
  }  

  // Weak version of lem_StrictDecrIFF
  // 0 < b < 1 ⟹ (x <= y ⟺ b^x >= b^y) 
  lemma lem_AntiMonoIncrIFF(b:R0, x:R0, y:R0)
    requires 0.0 < b < 1.0
    ensures x <= y <==> exp(b, x) >= exp(b, y)
  { 
    lem_StrictDecrIFFAuto();
  }

  lemma lem_AntiMonoIncrIFFAuto()
    ensures forall b:R0, x:R0, y:R0 :: 
      0.0 < b < 1.0 ==> (x <= y <==> exp(b, x) >= exp(b, y))
  {
    forall b:R0, x:R0, y:R0 | 0.0 < b < 1.0
      ensures x <= y <==> exp(b, x) >= exp(b, y)
    {
      lem_AntiMonoIncrIFF(b, x, y);
    }       
  }  

  /******************************************************************************
    Order properties on the base for exponent >= 0 (or > 0)
  ******************************************************************************/

  // Strictly increasing
  // e > 0 ∧ x,y >= 0 ∧ x < y ⟹ x^e < y^e
  lemma {:axiom} lem_BaseStrictIncr(e:real, x:real, y:real)
    requires e > 0.0 && x >= 0.0 && y >= 0.0
    ensures  x < y ==> exp(x, e) < exp(y, e)    

  lemma lem_BaseStrictIncrAuto()
    ensures forall e:real, x:real, y:real :: 
      e > 0.0 && x >= 0.0 && y >= 0.0 && x < y ==> exp(x, e) < exp(y, e)
  {
    forall e:real, x:real, y:real | e > 0.0 && x >= 0.0 && y >= 0.0
      ensures x < y ==> exp(x, e) < exp(y, e)
    {
      lem_BaseStrictIncr(e, x, y);
    }       
  }

  // Previous fact is reversible
  // e > 0 ∧ x,y >= 0 ∧ x^e < y^e ⟹ x < y
  lemma lem_BaseStrictIncrREV(e:real, x:real, y:real)
    requires e > 0.0 && x >= 0.0 && y >= 0.0
    ensures  exp(x, e) < exp(y, e) ==> x < y
  {
    var exp_e:real->real := (x => if x >= 0.0 then exp(x, e) else 0.0);
    assert forall x,y :: x >= 0.0 && y >= 0.0 ==> (x < y ==> exp_e(x) < exp_e(y))
      by { lem_BaseStrictIncrAuto(); } 
    lem_StrictIncrImpInjectiveRealPred(exp_e, (x => x >= 0.0));
    assert forall x,y :: x >= 0.0 && y >= 0.0 ==> (exp_e(x) < exp_e(y) ==> x < y);
    assert forall x :: x >= 0.0 ==> exp_e(x) == exp(x, e);    
  }

  lemma lem_BaseStrictIncrREVAuto()
    ensures forall e:real, x:real, y:real :: 
      e > 0.0 && x >= 0.0 && y >= 0.0 && exp(x, e) < exp(y, e) ==> x < y
  {
    forall e:real, x:real, y:real | e > 0.0 && x >= 0.0 && y >= 0.0
      ensures exp(x, e) < exp(y, e) ==> x < y 
    {
      lem_BaseStrictIncrREV(e, x, y);
    }       
  }

  // Join previous facts into an equivalence
  // e > 0 ∧ x,y >= 0 ⟹ (x < y ⟺ x^e < y^e)
  lemma lem_BaseStrictIncrIFF(e:real, x:real, y:real) 
    requires e > 0.0 && x >= 0.0 && y >= 0.0
    ensures  x < y <==> exp(x, e) < exp(y, e)
  { 
    lem_BaseStrictIncr(e,x,y);
    lem_BaseStrictIncrREV(e,x,y);
  }  

  lemma lem_BaseStrictIncrIFFAuto()
    ensures forall e:real, x:real, y:real :: 
      e > 0.0 && x >= 0.0 && y >= 0.0 ==> (x < y <==> exp(x, e) < exp(y, e))
  {
    forall e:real, x:real, y:real | e > 0.0 && x >= 0.0 && y >= 0.0
      ensures x < y <==> exp(x, e) < exp(y, e)
    {
      lem_BaseStrictIncrIFF(e, x, y);
    }       
  }

  // Weak version of lem_BaseStrictIncrIFF
  // e > 0 ∧ x,y >= 0 ⟹ (x <= y ⟺ x^e <= y^e)
  lemma lem_BaseMonoIncrIFF(e:real, x:real, y:real) 
    requires e > 0.0 && x >= 0.0 && y >= 0.0
    ensures  x <= y <==> exp(x, e) <= exp(y, e)
  { 
    lem_BaseStrictIncrIFFAuto();
  }  

  lemma lem_BaseMonoIncrIFFAuto()
    ensures forall e:real, x:real, y:real :: 
      e > 0.0 && x >= 0.0 && y >= 0.0 ==> (x <= y <==> exp(x, e) <= exp(y, e))
  {
    forall e:real, x:real, y:real | e > 0.0 && x >= 0.0 && y >= 0.0
      ensures x <= y <==> exp(x, e) <= exp(y, e)
    {
      lem_BaseMonoIncrIFF(e, x, y);
    }       
  }

  // A weak version of lem_BaseStrictIncr, also holds when x=0
  // but is restricted to x,y > 0
  // e >= 0 ∧ x,y > 0 ∧ x <= y ⟹ x^e <= y^e
  lemma lem_BaseMonoIncr(e:real, x:real, y:real)
    requires e >= 0.0 && x > 0.0 && y > 0.0
    ensures  x <= y ==> exp(x, e) <= exp(y, e)
  {
    if e == 0.0 {
      lem_Zero(x);
      lem_Zero(y);
    } else if e > 0.0 {
      lem_BaseStrictIncr(e, x, y);
    }    
  }

  lemma lem_BaseMonoIncrAuto()
    ensures forall e:real, x:real, y:real :: 
      e >= 0.0 && x > 0.0 && y > 0.0 && x <= y ==> exp(x, e) <= exp(y, e)
  {
    forall e:real, x:real, y:real | e >= 0.0 && x > 0.0 && y > 0.0
      ensures x <= y ==> exp(x, e) <= exp(y, e)
    {
      lem_BaseMonoIncr(e, x, y);
    }       
  }

  /******************************************************************************
    Tie the real-valued exp function to the natural-number version N.exp
    under overlapping domains
  ******************************************************************************/

  lemma lem_EqExpNat(b:nat, e:nat)
    requires b > 0
    ensures  N.exp(b, e) as R0 == exp(b as R0, e as R0)
  {
    if e == 0 {
      // BC: e = 0 
      calc {
           N.exp(b, 0) as R0;
        == { reveal N.exp(); }
           1.0;
        == { lem_Zero(b as R0); }
           exp(b as R0, 0.0);  
      }
    } else {
      // Step. e > 0
      //   IH: N.exp(b, e-1) = b^(e-1) 
      //    T:   N.exp(b, e) = b^e
      calc {
           N.exp(b, e) as R0;
        == { reveal N.exp(); }
           b as R0 * N.exp(b, e-1) as R0;
        == { lem_EqExpNat(b, e-1); }
           b as R0 * exp(b as R0, (e-1) as R0);  
        == { lem_Def(b as R0, (e-1) as R0); }    
           exp(b as R0, e as R0);  
      }
    }
  }

  lemma lem_EqExpNatAuto()
    ensures forall b:nat, e:nat :: 
      b > 0 ==> (N.exp(b, e) as R0 == exp(b as R0, e as R0))
  {
    forall b:nat, e:nat | b > 0
      ensures N.exp(b, e) as R0 == exp(b as R0, e as R0)
    {
      lem_EqExpNat(b, e);
    }       
  }  

  /******************************************************************************
    Special 2^x
  ******************************************************************************/

  // 2^x
  ghost function exp2(x:R0) : R0
  { 
    exp(2.0, x)
  }

  lemma lem_Exp2FirstValues()
    ensures exp2(0.0) == exp(2.0,0.0) == 1.0
    ensures exp2(1.0) == exp(2.0,1.0) == 2.0 
    ensures exp2(2.0) == exp(2.0,2.0) == 4.0
    ensures exp2(3.0) == exp(2.0,3.0) == 8.0
    ensures exp2(4.0) == exp(2.0,4.0) == 16.0
  {
    reveal exp2();
    lem_EqExpNat(2, 0);
    lem_EqExpNat(2, 1);
    lem_EqExpNat(2, 2);
    lem_EqExpNat(2, 3);
    lem_EqExpNat(2, 4);
    N.lem_Exp2FirstValues();
  }    

  // x < y ⟹ 2^x < 2^y
  lemma lem_exp2_StrictIncr(x:R0, y:R0)
    ensures x < y ==> exp2(x) < exp2(y)  
  {
    reveal exp2();
    lem_StrictIncr(2.0, x, y);
  }

  // 2^x < 2^y ⟹ x < y
  lemma lem_exp2_StrictIncrRev(x:R0, y:R0)
    ensures exp2(x) < exp2(y) ==> x < y
  {
    reveal exp2();
    lem_StrictIncrREV(2.0, x, y);
  }  

  // x < y ⟺ 2^x < 2^y 
  lemma lem_exp2_StrictIncrIFF(x:R0, y:R0)
    ensures x < y <==> exp2(x) < exp2(y) 
  {
    reveal exp2();
    lem_StrictIncrIFF(2.0, x, y);
  }    

  // x <= y ⟹ 2^x <= 2^y
  lemma lem_exp2_MonoIncr(x:R0, y:R0)
    ensures x <= y ==> exp2(x) <= exp2(y)  
  {
    lem_exp2_StrictIncr(x, y);
  }

}