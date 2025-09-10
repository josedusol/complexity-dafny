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
  // We assert lem_exp_NonNegative as post for convenience
  ghost function {:axiom} exp(x:real, y:real) : real
    ensures x >= 0.0 && y >= 0.0 ==> exp(x, y) >= 0.0

  // x,y >= 0 ⟹ x^y >= 0
  lemma {:axiom} lem_exp_NonNegative(x:real, y:real)
    requires x >= 0.0 && y >= 0.0
    ensures  exp(x, y) >= 0.0

  // x > 0 ⟹ x^y > 0
  lemma {:axiom} lem_exp_Positive(x:real, y:real)
    requires x > 0.0
    ensures  exp(x, y) > 0.0        

  // x > 1 ∧ y > 0 ⟹ x^y > 1
  lemma {:axiom} lem_exp_GTone(x:real, y:real)
    requires x > 1.0 && y > 0.0
    ensures  exp(x, y) > 1.0     

  // x^0 = 1
  lemma {:axiom} lem_exp_Zero(x:real)
    ensures exp(x, 0.0) == 1.0 

  // x >= 0 ⟹ x^1 = x
  lemma {:axiom} lem_exp_One(x:real)
    requires x >= 0.0
    ensures  exp(x, 1.0) == x    

  // y > 0 ⟹ 0^y = 0
  lemma {:axiom} lem_exp_BaseZero(y:real)
    requires y > 0.0
    ensures  exp(0.0, y) == 0.0     

  // 1^y = 1
  lemma {:axiom} lem_exp_BaseOne(y:real)
    ensures  exp(1.0, y) == 1.0     

  // x >= 0 ⟹ x^(y+z) = (x^y)*(x^z)
  lemma {:axiom} lem_exp_Product(x:real, y:real, z:real)
    requires x >= 0.0 
    ensures  exp(x, y+z) == exp(x, y)*exp(x, z)  

  // x >= 0 ⟹ (x^y)^z = x^(y*z)
  lemma {:axiom} lem_exp_Exp(x:real, y:real, z:real)
    requires x >= 0.0 
    ensures  exp(exp(x, y), z) == exp(x, y*z) 

  // x > 0 ⟹ x^(-k) = 1/x^k
  lemma {:axiom} lem_exp_Reciprocal(x:real, k:real) 
    requires x > 0.0
    requires exp(x, k) > 0.0
    ensures  exp(x, -k) == 1.0 / exp(x, k)

  // The only other axiom we take is lem_exp_BaseStrictIncr, see below in the list
  // of order properties on the base

  /******************************************************************************
    Universal closures of the axioms
  ******************************************************************************/

  lemma lem_exp_NonNegativeAuto()
    ensures forall x:real, y:real ::  
      x >= 0.0 && y >= 0.0 ==> exp(x, y) >= 0.0
  {
     forall x:real, y:real | x >= 0.0 && y >= 0.0
      ensures exp(x, y) >= 0.0
    {
      lem_exp_NonNegative(x, y);
    }
  }

  lemma lem_exp_PositiveAuto()
    ensures forall x:real, y:real ::  
            x > 0.0 && y >= 0.0 ==> exp(x, y) > 0.0
  {
     forall x:real, y:real | x > 0.0 && y >= 0.0
      ensures exp(x, y) > 0.0
    {
      lem_exp_Positive(x, y);
    }
  }  

  lemma lem_exp_GToneAuto()
    ensures forall x:real, y:real ::  
            x > 1.0 && y > 0.0 ==> exp(x, y) > 1.0
  {
     forall x:real, y:real | x > 1.0 && y > 0.0
      ensures exp(x, y) > 1.0
    {
      lem_exp_GTone(x, y);
    }
  } 

  lemma lem_exp_ZeroAuto()
    ensures forall x:real :: x >= 0.0 ==> exp(x, 0.0) == 1.0 
  {
    forall x:real | x >= 0.0
      ensures exp(x, 0.0) == 1.0 
    {
      lem_exp_Zero(x);
    }
  }

  lemma lem_exp_OneAuto()
    ensures forall x:real :: x >= 0.0 ==> exp(x, 1.0) == x 
  {
    forall x:real | x >= 0.0
      ensures exp(x, 1.0) == x 
    {
      lem_exp_One(x);
    }    
  }

  lemma lem_exp_BaseZeroAuto()
    ensures forall y:real :: y > 0.0 ==> exp(0.0, y) == 0.0 
  {
    forall y:real | y > 0.0
      ensures exp(0.0, y) == 0.0 
    {
      lem_exp_BaseZero(y);
    }
  }

  lemma lem_exp_BaseOneAuto()
    ensures forall y:real :: exp(1.0, y) == 1.0 
  {
    forall y:real
      ensures exp(1.0, y) == 1.0 
    {
      lem_exp_BaseOne(y);
    }
  }

  lemma lem_exp_ProductAuto()
    ensures forall x:real, y:real, z:real :: 
            x >= 0.0 ==> exp(x, y+z) == exp(x, y)*exp(x, z)
  {
    forall x:real, y:real, z:real | x >= 0.0
      ensures exp(x, y+z) == exp(x, y)*exp(x, z)
    {
      lem_exp_Product(x, y, z);
    }   
  }

  lemma lem_exp_ExpAuto()
    ensures forall x:real, y:real, z:real :: 
            x >= 0.0 ==> exp(exp(x, y), z) == exp(x, y*z) 
  {
    forall x:real, y:real, z:real | x >= 0.0
      ensures exp(exp(x, y), z) == exp(x, y*z) 
    {
      lem_exp_Exp(x, y, z);
    }   
  }

  lemma lem_exp_ReciprocalAuto()
    ensures forall x:real, k:real ::  
            x > 0.0 && exp(x, k) > 0.0 ==> exp(x, -k) == 1.0 / exp(x, k)
  {
     forall x:real, k:real | x > 0.0 && exp(x, k) > 0.0
      ensures exp(x, -k) == 1.0 / exp(x, k)
    {
      lem_exp_Reciprocal(x, k);
    }
  } 

  /******************************************************************************
    Derived properties
  ******************************************************************************/

  // x >= 1 ∧ y >= 0 ⟹ x^y >= 1
  lemma lem_exp_GEQone(x:real, y:real)
    requires x >= 1.0 && y >= 0.0
    ensures  exp(x, y) >= 1.0  
  {
    if y == 0.0 {
      lem_exp_Zero(x); 
    } else if y > 0.0 && x == 1.0 {
      lem_exp_BaseOne(y);
    } else if y > 0.0 && x > 1.0 {
      lem_exp_GTone(x, y);
    }
  }

  lemma lem_exp_GEQoneAuto()
    ensures forall x:real, y:real :: 
      x >= 1.0 && y >= 0.0 ==> exp(x, y) >= 1.0  
  {
    forall x:real, y:real | x >= 1.0 && y >= 0.0
      ensures exp(x, y) >= 1.0  
    {
      lem_exp_GEQone(x, y);
    }
  }

  // x >= 0 ⟹ x*(x^y) = x^(y+1)
  lemma lem_exp_Def(x:real, y:real)
    requires x >= 0.0
    ensures  x*exp(x, y) == exp(x, y + 1.0)
  { 
    calc {
          x*exp(x, y);
      == { lem_exp_One(x); }
          exp(x, 1.0)*exp(x, y);
      == { lem_exp_Product(x, 1.0, y); }
          exp(x, y + 1.0);
    } 
  } 

  lemma lem_exp_DefAuto()
    ensures forall x:real, y:real :: 
      x >= 0.0 ==> x*exp(x, y) == exp(x, y + 1.0)
  {
    forall x:real, y:real | x >= 0.0
      ensures x*exp(x, y) == exp(x, y + 1.0)
    {
      lem_exp_Def(x, y);
    }
  }

  /******************************************************************************
    Relate exp(x,0), exp(x,1), exp(x,2), etc. to Dafny primitive powers
  ******************************************************************************/

  // x >= 0 ⟹ x^0 = 1
  lemma lem_exp_Pow0(x:real) 
    requires x >= 0.0
    ensures  exp(x, 0.0) == 1.0
  { 
    lem_exp_Zero(x);
  }

  lemma lem_exp_Pow0Auto()
    ensures forall x:real :: x >= 0.0 ==> exp(x, 0.0) == 1.0
  {
    forall x:real | x >= 0.0
      ensures exp(x, 0.0) == 1.0
    {
      lem_exp_Pow0(x);
    }
  }

  // x >= 0 ⟹ x^1 = x
  lemma lem_exp_Pow1(x:real) 
    requires x >= 0.0
    ensures  exp(x, 1.0) == x
  { 
    lem_exp_One(x);
  }

  lemma lem_exp_Pow1Auto()
    ensures forall x:real :: x >= 0.0 ==> exp(x, 1.0) == x
  {
    forall x:real | x >= 0.0
      ensures exp(x, 1.0) == x
    {
      lem_exp_Pow1(x);
    }
  }

  // x >= 0 ⟹ x^2 = x*x
  lemma lem_exp_Pow2(x:real) 
    requires x >= 0.0
    ensures  exp(x, 2.0) == x*x
  {  
    calc {
         exp(x, 2.0);
      == { lem_exp_Product(x, 1.0, 1.0); }
         exp(x, 1.0)*exp(x, 1.0);
      == { lem_exp_One(x); }
         x*x;
    } 
  } 

  lemma lem_exp_Pow2Auto()
    ensures forall x:real :: x >= 0.0 ==> exp(x, 2.0) == x*x
  {
    forall x:real | x >= 0.0
      ensures exp(x, 2.0) == x*x
    {
      lem_exp_Pow2(x);
    }
  }

  // x >= 0 ⟹ x^3 = x*x*x
  lemma lem_exp_Pow3(x:real) 
    requires x >= 0.0
    ensures  exp(x, 3.0) == x*x*x
  {  
    calc {
         exp(x, 3.0);
      == { lem_exp_Product(x, 1.0, 2.0); }
         exp(x, 1.0)*exp(x, 2.0);
      == { lem_exp_Product(x, 1.0, 1.0); }
         exp(x, 1.0)*(exp(x, 1.0)*exp(x, 1.0));
      == { lem_exp_One(x); }
         x*(x*x);
      == x*x*x; 
    } 
  }   

  lemma lem_exp_Pow3Auto()
    ensures forall x:real :: x >= 0.0 ==> exp(x, 3.0) == x*x*x
  {
    forall x:real | x >= 0.0
      ensures exp(x, 3.0) == x*x*x
    {
      lem_exp_Pow3(x);
    }
  }

  /******************************************************************************
    Order properties on the exponent with base >= 1 (or > 1)
  ******************************************************************************/

  // Strictly increasing
  // b > 1 ∧ x < y ⟹ b^x < b^y
  lemma lem_exp_StrictIncr(b:real, x:real, y:real)
    requires b > 1.0
    ensures  x < y ==> exp(b, x) < exp(b, y)
  {
    if x < y {
      var d :| d > 0.0 && y == x + d
        by { lem_real_PosDifference(x, y); } 
      assert A: exp(b, x) > 0.0 by { lem_exp_Positive(b, x);}
      calc {
           exp(b, y);
        == { lem_exp_Product(b, x, d); }
           exp(b, x) * exp(b, d);
        >  { assert d > 0.0; lem_exp_GTone(b, d); reveal A; }
           exp(b, x) * 1.0;
        == exp(b, x);       
      }
    }
  }

  lemma lem_exp_StrictIncrAuto()
    ensures forall b:real, x:real, y:real :: 
      b > 1.0 && x < y ==> exp(b, x) < exp(b, y)
  {
    forall b:real, x:real, y:real | b > 1.0
      ensures x < y ==> exp(b, x) < exp(b, y)
    {
      lem_exp_StrictIncr(b, x, y);
    }       
  }

  // Previous fact is reversible
  // b > 1 ∧ b^x < b^y ⟹ x < y
  lemma lem_exp_StrictIncrRev(b:real, x:real, y:real)
    requires b > 1.0
    ensures  exp(b, x) < exp(b, y) ==> x < y
  { 
    var exp_b:real->real := (x => exp(b, x));
    assert forall x,y :: x < y ==> exp_b(x) < exp_b(y)
      by { lem_exp_StrictIncrAuto(); }
    lem_fun_StrictIncrIMPinjectiveReal(exp_b);
    assert forall x,y :: exp_b(x) < exp_b(y) ==> x < y;
    assert forall x :: exp_b(x) == exp(b, x);
  }

  lemma lem_exp_StrictIncrRevAuto()
    ensures forall b:real, x:real, y:real :: 
      b > 1.0 && exp(b, x) < exp(b, y) ==> x < y
  {
    forall b:real, x:real, y:real | b > 1.0
      ensures exp(b, x) < exp(b, y) ==> x < y
    {
      lem_exp_StrictIncrRev(b, x, y);
    }       
  }  

  // Join previous facts into an equivalence
  // b > 1 ⟹ (x < y ⟺ b^x < b^y)
  lemma lem_exp_StrictIncrIFF(b:real, x:real, y:real)
    requires b > 1.0
    ensures  x < y <==> exp(b, x) < exp(b, y)
  { 
    lem_exp_StrictIncr(b,x,y);
    lem_exp_StrictIncrRev(b,x,y);
  }

  lemma lem_exp_StrictIncrIFFAuto()
    ensures forall b:real, x:real, y:real :: 
      b > 1.0 ==> (x < y <==> exp(b, x) < exp(b, y))
  {
    forall b:real, x:real, y:real | b > 1.0
      ensures x < y <==> exp(b, x) < exp(b, y)
    {
      lem_exp_StrictIncrIFF(b, x, y);
    }       
  }    

  // Weak version of lem_exp_StrictIncrIFF
  // b > 1 ⟹ (x <= y ⟺ b^x <= b^y)
  lemma lem_exp_MonoIncrIFF(b:real, x:real, y:real)
    requires b > 1.0
    ensures  x <= y <==> exp(b, x) <= exp(b, y)
  {
    lem_exp_StrictIncrIFFAuto();
  }

  lemma lem_exp_MonoIncrIFFAuto()
    ensures forall b:real, x:real, y:real :: 
      b > 1.0 ==> (x <= y <==> exp(b, x) <= exp(b, y))
  {
    forall b:real, x:real, y:real | b > 1.0
      ensures x <= y <==> exp(b, x) <= exp(b, y)
    {
      lem_exp_MonoIncrIFF(b, x, y);
    }       
  }  

  // Weak version of lem_exp_StrictIncr, but also holds when x=1
  // b >= 1 ∧ x <= y ⟹ b^x <= b^y
  lemma lem_exp_MonoIncr(b:real, x:real, y:real)
    requires b >= 1.0
    ensures  x <= y ==> exp(b, x) <= exp(b, y)
  {
    if b == 1.0 {
      lem_exp_BaseOne(x);
      lem_exp_BaseOne(y);
    } else if b > 1.0 {
      lem_exp_StrictIncr(b, x, y);
    }    
  }

  /******************************************************************************
    Order properties on the exponent with base 0 < b < 1
  ******************************************************************************/

  // Strictly decreasing
  // 0 < b < 1 ∧ x < y ⟹ b^x > b^y   
  lemma {:axiom} lem_exp_StrictDecr(b:real, x:real, y:real)
    requires 0.0 < b < 1.0
    ensures x < y ==> exp(b, x) > exp(b, y) 

  lemma lem_exp_StrictDecrAuto()
    ensures forall b:real, x:real, y:real :: 
      0.0 < b < 1.0 && x < y ==> exp(b, x) > exp(b, y)
  {
    forall b:real, x:real, y:real | 0.0 < b < 1.0
      ensures x < y ==> exp(b, x) > exp(b, y)
    {
      lem_exp_StrictDecr(b, x, y);
    }       
  }

  // Previous fact is reversible
  // 0 < b < 1 ∧ b^x > b^y ⟹ x < y
  lemma lem_exp_StrictDecrRev(b:real, x:real, y:real)
    requires 0.0 < b < 1.0
    ensures exp(b, x) > exp(b, y) ==> x < y
  {
    var exp_b:real->real := (x => exp(b, x));
    assert forall x,y :: x < y ==> exp_b(x) > exp_b(y)
      by { lem_exp_StrictDecrAuto(); }
    lem_fun_StrictDecrIMPinjectiveReal(exp_b);
    assert forall x,y :: exp_b(x) > exp_b(y) ==> x < y;
    assert forall x :: exp_b(x) == exp(b, x);       
  }   

  lemma lem_exp_StrictDecrRevAuto()
    ensures forall b:real, x:real, y:real :: 
      0.0 < b < 1.0 && exp(b, x) > exp(b, y) ==> x < y
  {
    forall b:real, x:real, y:real | 0.0 < b < 1.0
      ensures exp(b, x) > exp(b, y) ==> x < y
    {
      lem_exp_StrictDecrRev(b, x, y);
    }             
  }  

  // Join previous facts into an equivalence
  // 0 < b < 1 ⟹ (x < y ⟺ b^x > b^y)  
  lemma lem_exp_StrictDecrIFF(b:real, x:real, y:real)
    requires 0.0 < b < 1.0
    ensures x < y <==> exp(b, x) > exp(b, y)
  {
    lem_exp_StrictDecr(b, x, y);
    lem_exp_StrictDecrRev(b, x, y);
  }

  lemma lem_exp_StrictDecrIFFAuto()
    ensures forall b:real, x:real, y:real :: 
      0.0 < b < 1.0 ==> (x < y <==> exp(b, x) > exp(b, y))
  {
    forall b:real, x:real, y:real | 0.0 < b < 1.0
      ensures x < y <==> exp(b, x) > exp(b, y)
    {
      lem_exp_StrictDecrIFF(b, x, y);
    }             
  }  

  // Weak version of lem_exp_StrictDecrIFF
  // 0 < b < 1 ⟹ (x <= y ⟺ b^x >= b^y) 
  lemma lem_exp_AntiMonoIncrIFF(b:real, x:real, y:real)
    requires 0.0 < b < 1.0
    ensures x <= y <==> exp(b, x) >= exp(b, y)
  { 
    lem_exp_StrictDecrIFFAuto();
  }

  lemma lem_exp_AntiMonoIncrIFFAuto()
    ensures forall b:real, x:real, y:real :: 
      0.0 < b < 1.0 ==> (x <= y <==> exp(b, x) >= exp(b, y))
  {
    forall b:real, x:real, y:real | 0.0 < b < 1.0
      ensures x <= y <==> exp(b, x) >= exp(b, y)
    {
      lem_exp_AntiMonoIncrIFF(b, x, y);
    }       
  }  

  /******************************************************************************
    Order properties on the base for exponent >= 0 (or > 0)
  ******************************************************************************/

  // Strictly increasing
  // e > 0 ∧ x,y >= 0 ∧ x < y ⟹ x^e < y^e
  lemma {:axiom} lem_exp_BaseStrictIncr(e:real, x:real, y:real)
    requires e > 0.0 && x >= 0.0 && y >= 0.0
    ensures  x < y ==> exp(x, e) < exp(y, e)    

  lemma lem_exp_BaseStrictIncrAuto()
    ensures forall e:real, x:real, y:real :: 
      e > 0.0 && x >= 0.0 && y >= 0.0 && x < y ==> exp(x, e) < exp(y, e)
  {
    forall e:real, x:real, y:real | e > 0.0 && x >= 0.0 && y >= 0.0
      ensures x < y ==> exp(x, e) < exp(y, e)
    {
      lem_exp_BaseStrictIncr(e, x, y);
    }       
  }

  // Previous fact is reversible
  // e > 0 ∧ x,y >= 0 ∧ x^e < y^e ⟹ x < y
  lemma lem_exp_BaseStrictIncrRev(e:real, x:real, y:real)
    requires e > 0.0 && x >= 0.0 && y >= 0.0
    ensures  exp(x, e) < exp(y, e) ==> x < y
  {
    var exp_e:real->real := (x => exp(x, e));
    assert forall x,y :: x >= 0.0 && y >= 0.0 ==> (x < y ==> exp_e(x) < exp_e(y))
      by { lem_exp_BaseStrictIncrAuto(); } 
    lem_fun_StrictIncrIMPinjectiveRealPred(exp_e, (x => x >= 0.0));
    assert forall x,y :: x >= 0.0 && y >= 0.0 ==> (exp_e(x) < exp_e(y) ==> x < y);
    assert forall x :: exp_e(x) == exp(x, e);    
  }

  lemma lem_exp_BaseStrictIncrRevAuto()
    ensures forall e:real, x:real, y:real :: 
      e > 0.0 && x >= 0.0 && y >= 0.0 && exp(x, e) < exp(y, e) ==> x < y
  {
    forall e:real, x:real, y:real | e > 0.0 && x >= 0.0 && y >= 0.0
      ensures exp(x, e) < exp(y, e) ==> x < y 
    {
      lem_exp_BaseStrictIncrRev(e, x, y);
    }       
  }

  // Join previous facts into an equivalence
  // e > 0 ∧ x,y >= 0 ⟹ (x < y ⟺ x^e < y^e)
  lemma lem_exp_BaseStrictIncrIFF(e:real, x:real, y:real) 
    requires e > 0.0 && x >= 0.0 && y >= 0.0
    ensures  x < y <==> exp(x, e) < exp(y, e)
  { 
    lem_exp_BaseStrictIncr(e,x,y);
    lem_exp_BaseStrictIncrRev(e,x,y);
  }  

  lemma lem_exp_BaseStrictIncrIFFAuto()
    ensures forall e:real, x:real, y:real :: 
      e > 0.0 && x >= 0.0 && y >= 0.0 ==> (x < y <==> exp(x, e) < exp(y, e))
  {
    forall e:real, x:real, y:real | e > 0.0 && x >= 0.0 && y >= 0.0
      ensures x < y <==> exp(x, e) < exp(y, e)
    {
      lem_exp_BaseStrictIncrIFF(e, x, y);
    }       
  }

  // Weak version of lem_exp_BaseStrictIncrIFF
  // e > 0 ∧ x,y >= 0 ⟹ (x <= y ⟺ x^e <= y^e)
  lemma lem_exp_BaseMonoIncrIFF(e:real, x:real, y:real) 
    requires e > 0.0 && x >= 0.0 && y >= 0.0
    ensures  x <= y <==> exp(x, e) <= exp(y, e)
  { 
    lem_exp_BaseStrictIncrIFFAuto();
  }  

  lemma lem_exp_BaseMonoIncrIFFAuto()
    ensures forall e:real, x:real, y:real :: 
      e > 0.0 && x >= 0.0 && y >= 0.0 ==> (x <= y <==> exp(x, e) <= exp(y, e))
  {
    forall e:real, x:real, y:real | e > 0.0 && x >= 0.0 && y >= 0.0
      ensures x <= y <==> exp(x, e) <= exp(y, e)
    {
      lem_exp_BaseMonoIncrIFF(e, x, y);
    }       
  }

  // A weak version of lem_exp_BaseStrictIncr, also holds when x=0
  // but is restricted to x,y > 0
  // e >= 0 ∧ x,y > 0 ∧ x <= y ⟹ x^e <= y^e
  lemma lem_exp_BaseMonoIncr(e:real, x:real, y:real)
    requires e >= 0.0 && x > 0.0 && y > 0.0
    ensures  x <= y ==> exp(x, e) <= exp(y, e)
  {
    if e == 0.0 {
      lem_exp_Zero(x);
      lem_exp_Zero(y);
    } else if e > 0.0 {
      lem_exp_BaseStrictIncr(e, x, y);
    }    
  }

  lemma lem_exp_BaseMonoIncrAuto()
    ensures forall e:real, x:real, y:real :: 
      e >= 0.0 && x > 0.0 && y > 0.0 && x <= y ==> exp(x, e) <= exp(y, e)
  {
    forall e:real, x:real, y:real | e >= 0.0 && x > 0.0 && y > 0.0
      ensures x <= y ==> exp(x, e) <= exp(y, e)
    {
      lem_exp_BaseMonoIncr(e, x, y);
    }       
  }

  /******************************************************************************
    Tie the real-valued exp function to the natural-number version N.exp
    under overlapping domains
  ******************************************************************************/

  lemma lem_exp_OverNat(b:nat, e:nat)
    requires b > 0
    ensures  N.exp(b, e) as real == exp(b as real, e as real)
  {
    if e == 0 {
      // BC: e = 0 
      calc {
           N.exp(b, 0) as real;
        == { reveal N.exp(); }
           1.0;
        == { lem_exp_Zero(b as real); }
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
        == { lem_exp_OverNat(b, e-1); }
           b as real * exp(b as real, (e-1) as real);  
        == { lem_exp_Def(b as real, (e-1) as real); }    
           exp(b as real, e as real);  
      }
    }
  }

  lemma lem_exp_OverNatAuto()
    ensures forall b:nat, e:nat :: 
      b > 0 ==> (N.exp(b, e) as real == exp(b as real, e as real))
  {
    forall b:nat, e:nat | b > 0
      ensures N.exp(b, e) as real == exp(b as real, e as real)
    {
      lem_exp_OverNat(b, e);
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

  lemma lem_exp2_FirstValues()
    ensures exp2(0.0) == exp(2.0,0.0) == 1.0
    ensures exp2(1.0) == exp(2.0,1.0) == 2.0 
    ensures exp2(2.0) == exp(2.0,2.0) == 4.0
    ensures exp2(3.0) == exp(2.0,3.0) == 8.0
    ensures exp2(4.0) == exp(2.0,4.0) == 16.0
  {
    reveal exp2();
    lem_exp_OverNat(2, 0);
    lem_exp_OverNat(2, 1);
    lem_exp_OverNat(2, 2);
    lem_exp_OverNat(2, 3);
    lem_exp_OverNat(2, 4);
    N.lem_exp2_FirstValues();
  }    

  // x < y ⟹ 2^x < 2^y
  lemma lem_exp2_StrictIncr(x:real, y:real)
    ensures x < y ==> exp2(x) < exp2(y)  
  {
    reveal exp2();
    lem_exp_StrictIncr(2.0, x, y);
  }

  // 2^x < 2^y ⟹ x < y
  lemma lem_exp2_StrictIncrRev(x:real, y:real)
    ensures exp2(x) < exp2(y) ==> x < y
  {
    reveal exp2();
    lem_exp_StrictIncrRev(2.0, x, y);
  }  

  // x < y <==> 2^x < 2^y 
  lemma lem_exp2_StrictIncrIFF(x:real, y:real)
    ensures x < y <==> exp2(x) < exp2(y) 
  {
    reveal exp2();
    lem_exp_StrictIncrIFF(2.0, x, y);
  }    

  // x <= y ⟹ 2^x <= 2^y
  lemma lem_exp2_MonoIncr(x:real, y:real)
    ensures x <= y ==> exp2(x) <= exp2(y)  
  {
    lem_exp2_StrictIncr(x, y);
  }

}