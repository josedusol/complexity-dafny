include "./ExpNat.dfy"
include "./LemFunction.dfy"
include "./LemReal.dfy"

/******************************************************************************
  Exponentiation over reals
******************************************************************************/

// A basic axiomatization of exp over non-negative reals would consist of at least
// the following propositions:
//
// Zero exponent law 
//   x^0 = 1
// One exponent law
//   x^1 = x
// Product of exponents (power rule)
//   x^(y+z) = (x^y)*(x^z) 
// Power of a power
//   (x^y)^z = x^(y*z)
//
// However, we want to allow negative exponents. 
// So we define exp more generally over all reals, and axiomatize its behaviour 
// mainly for the non-negative case with appropiate restrictions. 
// Following typical algebra treatment and Knuth's advice we have 0^0=1.
// The Non-Negative axiom ensures a non-negative range:
//   x,y >= 0 ⟹ x^y >= 0 
// For negative exponents we also add an axiom for reciprocals:
//   x > 0 ⟹ x^-k == 1/x^k 
//
// As a consequence, something like "(-2.0)^y" is valid syntax but undefined
// so we can't claim anything about it.

module ExpReal {

  import N = ExpNat
  import opened LemFunction
  import opened LemReal

  // x^y
  // We assert lem_NonNegative as post for convenience
  ghost function {:axiom} exp(x:real, y:real) : real
    ensures x >= 0.0 && y >= 0.0 ==> exp(x, y) >= 0.0

  // x,y >= 0 ⟹ x^y >= 0
  lemma {:axiom} lem_NonNegative(x:real, y:real)
    requires x >= 0.0 && y >= 0.0
    ensures  exp(x, y) >= 0.0

  // x > 0 ⟹ x^y > 0
  lemma {:axiom} lem_Positive(x:real, y:real)
    requires x > 0.0
    ensures  exp(x, y) > 0.0        

  // x > 1 ∧ y > 0 ⟹ x^y > 1
  lemma {:axiom} lem_GTone(x:real, y:real)
    requires x > 1.0 && y > 0.0
    ensures  exp(x, y) > 1.0     

  // x^0 = 1
  lemma {:axiom} lem_Zero(x:real)
    ensures exp(x, 0.0) == 1.0 

  // x >= 0 ⟹ x^1 = x
  lemma {:axiom} lem_One(x:real)
    requires x >= 0.0
    ensures  exp(x, 1.0) == x    

  // y > 0 ⟹ 0^y = 0
  lemma {:axiom} lem_BaseZero(y:real)
    requires y > 0.0
    ensures  exp(0.0, y) == 0.0     

  // 1^y = 1
  lemma {:axiom} lem_BaseOne(y:real)
    ensures  exp(1.0, y) == 1.0     

  // x >= 0 ⟹ x^(y+z) = (x^y)*(x^z)
  lemma {:axiom} lem_Product(x:real, y:real, z:real)
    requires x >= 0.0 
    ensures  exp(x, y+z) == exp(x, y)*exp(x, z)  

  // x >= 0 ⟹ (x^y)^z = x^(y*z)
  lemma {:axiom} lem_Exp(x:real, y:real, z:real)
    requires x >= 0.0 
    ensures  exp(exp(x, y), z) == exp(x, y*z) 

  // x > 0 ⟹ x^(-k) = 1/x^k
  lemma {:axiom} lem_Reciprocal(x:real, k:real) 
    requires x > 0.0
    requires exp(x, k) > 0.0
    ensures  exp(x, -k) == 1.0 / exp(x, k)

  // The only other axiom we take is lem_BaseStrictIncr, see below in the list
  // of order properties on the base

  /******************************************************************************
    Universal closures of the axioms
  ******************************************************************************/

  lemma lem_NonNegativeAuto()
    ensures forall x:real, y:real ::  
      x >= 0.0 && y >= 0.0 ==> exp(x, y) >= 0.0
  {
     forall x:real, y:real | x >= 0.0 && y >= 0.0
      ensures exp(x, y) >= 0.0
    {
      lem_NonNegative(x, y);
    }
  }

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
    ensures forall x:real, y:real ::  
            x > 1.0 && y > 0.0 ==> exp(x, y) > 1.0
  {
     forall x:real, y:real | x > 1.0 && y > 0.0
      ensures exp(x, y) > 1.0
    {
      lem_GTone(x, y);
    }
  } 

  lemma lem_ZeroAuto()
    ensures forall x:real :: x >= 0.0 ==> exp(x, 0.0) == 1.0 
  {
    forall x:real | x >= 0.0
      ensures exp(x, 0.0) == 1.0 
    {
      lem_Zero(x);
    }
  }

  lemma lem_OneAuto()
    ensures forall x:real :: x >= 0.0 ==> exp(x, 1.0) == x 
  {
    forall x:real | x >= 0.0
      ensures exp(x, 1.0) == x 
    {
      lem_One(x);
    }    
  }

  lemma lem_BaseZeroAuto()
    ensures forall y:real :: y > 0.0 ==> exp(0.0, y) == 0.0 
  {
    forall y:real | y > 0.0
      ensures exp(0.0, y) == 0.0 
    {
      lem_BaseZero(y);
    }
  }

  lemma lem_BaseOneAuto()
    ensures forall y:real :: exp(1.0, y) == 1.0 
  {
    forall y:real
      ensures exp(1.0, y) == 1.0 
    {
      lem_BaseOne(y);
    }
  }

  lemma lem_ProductAuto()
    ensures forall x:real, y:real, z:real :: 
            x >= 0.0 ==> exp(x, y+z) == exp(x, y)*exp(x, z)
  {
    forall x:real, y:real, z:real | x >= 0.0
      ensures exp(x, y+z) == exp(x, y)*exp(x, z)
    {
      lem_Product(x, y, z);
    }   
  }

  lemma lem_ExpAuto()
    ensures forall x:real, y:real, z:real :: 
            x >= 0.0 ==> exp(exp(x, y), z) == exp(x, y*z) 
  {
    forall x:real, y:real, z:real | x >= 0.0
      ensures exp(exp(x, y), z) == exp(x, y*z) 
    {
      lem_Exp(x, y, z);
    }   
  }

  lemma lem_ReciprocalAuto()
    ensures forall x:real, k:real ::  
            x > 0.0 && exp(x, k) > 0.0 ==> exp(x, -k) == 1.0 / exp(x, k)
  {
     forall x:real, k:real | x > 0.0 && exp(x, k) > 0.0
      ensures exp(x, -k) == 1.0 / exp(x, k)
    {
      lem_Reciprocal(x, k);
    }
  } 

  /******************************************************************************
    Derived properties
  ******************************************************************************/

  // x >= 1 ∧ y >= 0 ⟹ x^y >= 1
  lemma lem_GEQone(x:real, y:real)
    requires x >= 1.0 && y >= 0.0
    ensures  exp(x, y) >= 1.0  
  {
    if y == 0.0 {
      lem_Zero(x); 
    } else if y > 0.0 && x == 1.0 {
      lem_BaseOne(y);
    } else if y > 0.0 && x > 1.0 {
      lem_GTone(x, y);
    }
  }

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

  // x >= 0 ⟹ x*(x^y) = x^(y+1)
  lemma lem_Def(x:real, y:real)
    requires x >= 0.0
    ensures  x*exp(x, y) == exp(x, y + 1.0)
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
    ensures forall x:real, y:real :: 
      x >= 0.0 ==> x*exp(x, y) == exp(x, y + 1.0)
  {
    forall x:real, y:real | x >= 0.0
      ensures x*exp(x, y) == exp(x, y + 1.0)
    {
      lem_Def(x, y);
    }
  }

  /******************************************************************************
    Relate exp(x,0), exp(x,1), exp(x,2), etc. to Dafny primitive powers
  ******************************************************************************/

  // x >= 0 ⟹ x^0 = 1
  lemma lem_Pow0(x:real) 
    requires x >= 0.0
    ensures  exp(x, 0.0) == 1.0
  { 
    lem_Zero(x);
  }

  lemma lem_Pow0Auto()
    ensures forall x:real :: x >= 0.0 ==> exp(x, 0.0) == 1.0
  {
    forall x:real | x >= 0.0
      ensures exp(x, 0.0) == 1.0
    {
      lem_Pow0(x);
    }
  }

  // x >= 0 ⟹ x^1 = x
  lemma lem_Pow1(x:real) 
    requires x >= 0.0
    ensures  exp(x, 1.0) == x
  { 
    lem_One(x);
  }

  lemma lem_Pow1Auto()
    ensures forall x:real :: x >= 0.0 ==> exp(x, 1.0) == x
  {
    forall x:real | x >= 0.0
      ensures exp(x, 1.0) == x
    {
      lem_Pow1(x);
    }
  }

  // x >= 0 ⟹ x^2 = x*x
  lemma lem_Pow2(x:real) 
    requires x >= 0.0
    ensures  exp(x, 2.0) == x*x
  {  
    calc {
         exp(x, 2.0);
      == { lem_Product(x, 1.0, 1.0); }
         exp(x, 1.0)*exp(x, 1.0);
      == { lem_One(x); }
         x*x;
    } 
  } 

  lemma lem_Pow2Auto()
    ensures forall x:real :: x >= 0.0 ==> exp(x, 2.0) == x*x
  {
    forall x:real | x >= 0.0
      ensures exp(x, 2.0) == x*x
    {
      lem_Pow2(x);
    }
  }

  // x >= 0 ⟹ x^3 = x*x*x
  lemma lem_Pow3(x:real) 
    requires x >= 0.0
    ensures  exp(x, 3.0) == x*x*x
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
    ensures forall x:real :: x >= 0.0 ==> exp(x, 3.0) == x*x*x
  {
    forall x:real | x >= 0.0
      ensures exp(x, 3.0) == x*x*x
    {
      lem_Pow3(x);
    }
  }

  /******************************************************************************
    Order properties on the exponent with base >= 1 (or > 1)
  ******************************************************************************/

  // Strictly increasing
  // b > 1 ∧ x < y ⟹ b^x < b^y
  lemma lem_StrictIncr(b:real, x:real, y:real)
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
    ensures forall b:real, x:real, y:real :: 
      b > 1.0 && x < y ==> exp(b, x) < exp(b, y)
  {
    forall b:real, x:real, y:real | b > 1.0
      ensures x < y ==> exp(b, x) < exp(b, y)
    {
      lem_StrictIncr(b, x, y);
    }       
  }

  // Previous fact is reversible
  // b > 1 ∧ b^x < b^y ⟹ x < y
  lemma lem_StrictIncrREV(b:real, x:real, y:real)
    requires b > 1.0
    ensures  exp(b, x) < exp(b, y) ==> x < y
  { 
    var exp_b:real->real := (x => exp(b, x));
    assert forall x,y :: x < y ==> exp_b(x) < exp_b(y)
      by { lem_StrictIncrAuto(); }
    lem_StrictIncrImpInjectiveReal(exp_b);
    assert forall x,y :: exp_b(x) < exp_b(y) ==> x < y;
    assert forall x :: exp_b(x) == exp(b, x);
  }

  lemma lem_StrictIncrREVAuto()
    ensures forall b:real, x:real, y:real :: 
      b > 1.0 && exp(b, x) < exp(b, y) ==> x < y
  {
    forall b:real, x:real, y:real | b > 1.0
      ensures exp(b, x) < exp(b, y) ==> x < y
    {
      lem_StrictIncrREV(b, x, y);
    }       
  }  

  // Join previous facts into an equivalence
  // b > 1 ⟹ (x < y ⟺ b^x < b^y)
  lemma lem_StrictIncrIFF(b:real, x:real, y:real)
    requires b > 1.0
    ensures  x < y <==> exp(b, x) < exp(b, y)
  { 
    lem_StrictIncr(b,x,y);
    lem_StrictIncrREV(b,x,y);
  }

  lemma lem_StrictIncrIFFAuto()
    ensures forall b:real, x:real, y:real :: 
      b > 1.0 ==> (x < y <==> exp(b, x) < exp(b, y))
  {
    forall b:real, x:real, y:real | b > 1.0
      ensures x < y <==> exp(b, x) < exp(b, y)
    {
      lem_StrictIncrIFF(b, x, y);
    }       
  }    

  // Weak version of lem_StrictIncrIFF
  // b > 1 ⟹ (x <= y ⟺ b^x <= b^y)
  lemma lem_MonoIncrIFF(b:real, x:real, y:real)
    requires b > 1.0
    ensures  x <= y <==> exp(b, x) <= exp(b, y)
  {
    lem_StrictIncrIFFAuto();
  }

  lemma lem_MonoIncrIFFAuto()
    ensures forall b:real, x:real, y:real :: 
      b > 1.0 ==> (x <= y <==> exp(b, x) <= exp(b, y))
  {
    forall b:real, x:real, y:real | b > 1.0
      ensures x <= y <==> exp(b, x) <= exp(b, y)
    {
      lem_MonoIncrIFF(b, x, y);
    }       
  }  

  // Weak version of lem_StrictIncr, but also holds when x=1
  // b >= 1 ∧ x <= y ⟹ b^x <= b^y
  lemma lem_MonoIncr(b:real, x:real, y:real)
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
  lemma {:axiom} lem_StrictDecr(b:real, x:real, y:real)
    requires 0.0 < b < 1.0
    ensures x < y ==> exp(b, x) > exp(b, y) 

  lemma lem_StrictDecrAuto()
    ensures forall b:real, x:real, y:real :: 
      0.0 < b < 1.0 && x < y ==> exp(b, x) > exp(b, y)
  {
    forall b:real, x:real, y:real | 0.0 < b < 1.0
      ensures x < y ==> exp(b, x) > exp(b, y)
    {
      lem_StrictDecr(b, x, y);
    }       
  }

  // Previous fact is reversible
  // 0 < b < 1 ∧ b^x > b^y ⟹ x < y
  lemma lem_StrictDecrREV(b:real, x:real, y:real)
    requires 0.0 < b < 1.0
    ensures exp(b, x) > exp(b, y) ==> x < y
  {
    var exp_b:real->real := (x => exp(b, x));
    assert forall x,y :: x < y ==> exp_b(x) > exp_b(y)
      by { lem_StrictDecrAuto(); }
    lem_StrictDecrImpInjectiveReal(exp_b);
    assert forall x,y :: exp_b(x) > exp_b(y) ==> x < y;
    assert forall x :: exp_b(x) == exp(b, x);       
  }   

  lemma lem_StrictDecrREVAuto()
    ensures forall b:real, x:real, y:real :: 
      0.0 < b < 1.0 && exp(b, x) > exp(b, y) ==> x < y
  {
    forall b:real, x:real, y:real | 0.0 < b < 1.0
      ensures exp(b, x) > exp(b, y) ==> x < y
    {
      lem_StrictDecrREV(b, x, y);
    }             
  }  

  // Join previous facts into an equivalence
  // 0 < b < 1 ⟹ (x < y ⟺ b^x > b^y)  
  lemma lem_StrictDecrIFF(b:real, x:real, y:real)
    requires 0.0 < b < 1.0
    ensures x < y <==> exp(b, x) > exp(b, y)
  {
    lem_StrictDecr(b, x, y);
    lem_StrictDecrREV(b, x, y);
  }

  lemma lem_StrictDecrIFFAuto()
    ensures forall b:real, x:real, y:real :: 
      0.0 < b < 1.0 ==> (x < y <==> exp(b, x) > exp(b, y))
  {
    forall b:real, x:real, y:real | 0.0 < b < 1.0
      ensures x < y <==> exp(b, x) > exp(b, y)
    {
      lem_StrictDecrIFF(b, x, y);
    }             
  }  

  // Weak version of lem_StrictDecrIFF
  // 0 < b < 1 ⟹ (x <= y ⟺ b^x >= b^y) 
  lemma lem_AntiMonoIncrIFF(b:real, x:real, y:real)
    requires 0.0 < b < 1.0
    ensures x <= y <==> exp(b, x) >= exp(b, y)
  { 
    lem_StrictDecrIFFAuto();
  }

  lemma lem_AntiMonoIncrIFFAuto()
    ensures forall b:real, x:real, y:real :: 
      0.0 < b < 1.0 ==> (x <= y <==> exp(b, x) >= exp(b, y))
  {
    forall b:real, x:real, y:real | 0.0 < b < 1.0
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
    var exp_e:real->real := (x => exp(x, e));
    assert forall x,y :: x >= 0.0 && y >= 0.0 ==> (x < y ==> exp_e(x) < exp_e(y))
      by { lem_BaseStrictIncrAuto(); } 
    lem_StrictIncrImpInjectiveRealPred(exp_e, (x => x >= 0.0));
    assert forall x,y :: x >= 0.0 && y >= 0.0 ==> (exp_e(x) < exp_e(y) ==> x < y);
    assert forall x :: exp_e(x) == exp(x, e);    
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
    ensures  N.exp(b, e) as real == exp(b as real, e as real)
  {
    if e == 0 {
      // BC: e = 0 
      calc {
           N.exp(b, 0) as real;
        == { reveal N.exp(); }
           1.0;
        == { lem_Zero(b as real); }
           exp(b as real, 0.0);  
      }
    } else {
      // Step. e > 0
      //   IH: N.exp(b, e-1) = b^(e-1) 
      //    T:   N.exp(b, e) = b^e
      calc {
           N.exp(b, e) as real;
        == { reveal N.exp(); }
           b as real * N.exp(b, e-1) as real;
        == { lem_EqExpNat(b, e-1); }
           b as real * exp(b as real, (e-1) as real);  
        == { lem_Def(b as real, (e-1) as real); }    
           exp(b as real, e as real);  
      }
    }
  }

  lemma lem_EqExpNatAuto()
    ensures forall b:nat, e:nat :: 
      b > 0 ==> (N.exp(b, e) as real == exp(b as real, e as real))
  {
    forall b:nat, e:nat | b > 0
      ensures N.exp(b, e) as real == exp(b as real, e as real)
    {
      lem_EqExpNat(b, e);
    }       
  }  

  /******************************************************************************
    Special 2^x
  ******************************************************************************/

  // 2^x
  ghost function exp2(x:real) : real
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
  lemma lem_exp2_StrictIncr(x:real, y:real)
    ensures x < y ==> exp2(x) < exp2(y)  
  {
    reveal exp2();
    lem_StrictIncr(2.0, x, y);
  }

  // 2^x < 2^y ⟹ x < y
  lemma lem_exp2_StrictIncrRev(x:real, y:real)
    ensures exp2(x) < exp2(y) ==> x < y
  {
    reveal exp2();
    lem_StrictIncrREV(2.0, x, y);
  }  

  // x < y <==> 2^x < 2^y 
  lemma lem_exp2_StrictIncrIFF(x:real, y:real)
    ensures x < y <==> exp2(x) < exp2(y) 
  {
    reveal exp2();
    lem_StrictIncrIFF(2.0, x, y);
  }    

  // x <= y ⟹ 2^x <= 2^y
  lemma lem_exp2_MonoIncr(x:real, y:real)
    ensures x <= y ==> exp2(x) <= exp2(y)  
  {
    lem_exp2_StrictIncr(x, y);
  }

}