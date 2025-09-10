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
  lemma {:axiom} lem_exp_Positive(x:R0, y:R0)
    requires x > 0.0
    ensures  exp(x, y) > 0.0         

  // x > 1 ∧ y > 0 ⟹ x^y > 1
  lemma {:axiom} lem_exp_GTone(x:R0, y:R0)
    requires x > 1.0 && y > 0.0
    ensures  exp(x, y) > 1.0     

  // x^0 = 1
  lemma {:axiom} lem_exp_Zero(x:R0)
    ensures  exp(x, 0.0) == 1.0 

  // x^1 = x
  lemma {:axiom} lem_exp_One(x:R0)
    ensures  exp(x, 1.0) == x

  // y > 0 ⟹ 0^y = 0
  lemma {:axiom} lem_exp_BaseZero(y:R0)
    requires y > 0.0
    ensures  exp(0.0, y) == 0.0     

  // 1^y = 1
  lemma {:axiom} lem_exp_BaseOne(y:R0)
    ensures  exp(1.0, y) == 1.0     

  // x^(y+z) = (x^y)*(x^z)
  lemma {:axiom} lem_exp_Product(x:R0, y:R0, z:R0)
    ensures  exp(x, y+z) == exp(x, y)*exp(x, z)  

  // (x^y)^z = x^(y*z)
  lemma {:axiom} lem_exp_Exp(x:R0, y:R0, z:R0)
    ensures  exp(exp(x, y), z) == exp(x, y*z) 

  // The only other axiom we take is lem_exp_BaseStrictIncr, see below in the list
  // of order properties on the base

  /******************************************************************************
    Universal closures of the axioms
  ******************************************************************************/

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
    ensures forall x:R0, y:R0 ::  
            x > 1.0 && y > 0.0 ==> exp(x, y) > 1.0
  {
     forall x:R0, y:R0 | x > 1.0 && y > 0.0
      ensures exp(x, y) > 1.0
    {
      lem_exp_GTone(x, y);
    }
  } 

  lemma lem_exp_ZeroAuto()
    ensures forall x:R0 :: x > 0.0 ==> exp(x, 0.0) == 1.0 
  {
    forall x:R0 | x > 0.0
      ensures exp(x, 0.0) == 1.0 
    {
      lem_exp_Zero(x);
    }
  }

  lemma lem_exp_OneAuto()
    ensures forall x:R0 :: x > 0.0 ==> exp(x, 1.0) == x 
  {
    forall x:R0 | x > 0.0
      ensures exp(x, 1.0) == x 
    {
      lem_exp_One(x);
    }    
  }

  lemma lem_exp_BaseZeroAuto()
    ensures forall y:R0 :: y > 0.0 ==> exp(0.0, y) == 0.0 
  {
    forall y:R0 | y > 0.0
      ensures exp(0.0, y) == 0.0 
    {
      lem_exp_BaseZero(y);
    }
  }

  lemma lem_exp_BaseOneAuto()
    ensures forall y:R0 :: exp(1.0, y) == 1.0 
  {
    forall y:R0
      ensures exp(1.0, y) == 1.0 
    {
      lem_exp_BaseOne(y);
    }
  }

  lemma lem_exp_ProductAuto()
    ensures forall x:R0, y:R0, z:R0 :: 
      exp(x, y+z) == exp(x, y)*exp(x, z)
  {
    forall x:R0, y:R0, z:R0
      ensures exp(x, y+z) == exp(x, y)*exp(x, z)
    {
      lem_exp_Product(x, y, z);
    }   
  }

  lemma lem_exp_ExpAuto()
    ensures forall x:R0, y:R0, z:R0 :: 
            x >= 0.0 ==> exp(exp(x, y), z) == exp(x, y*z) 
  {
    forall x:R0, y:R0, z:R0 | x >= 0.0
      ensures exp(exp(x, y), z) == exp(x, y*z) 
    {
      lem_exp_Exp(x, y, z);
    }   
  }

  /******************************************************************************
    Derived properties
  ******************************************************************************/

  // x >= 1 ⟹ x^y >= 1
  lemma {:axiom} lem_exp_GEQone(x:R0, y:R0)
    requires x >= 1.0
    ensures  exp(x, y) >= 1.0  

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

  // x*(x^y) = x^(y+1)
  lemma lem_exp_Def(x:R0, y:R0)
    ensures x*exp(x, y) == exp(x, y + 1.0)
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
    ensures forall x:R0, y:R0 :: 
      x*exp(x, y) == exp(x, y + 1.0)
  {
    forall x:R0, y:R0
      ensures x*exp(x, y) == exp(x, y + 1.0)
    {
      lem_exp_Def(x, y);
    }
  }

  /******************************************************************************
    Relate exp(x,0), exp(x,1), exp(x,2), etc. to Dafny primitive powers
  ******************************************************************************/

  // x^0 = 1
  lemma lem_exp_Pow0(x:R0) 
    ensures exp(x, 0.0) == 1.0
  { 
    lem_exp_Zero(x);
  }

  lemma lem_exp_Pow0Auto()
    ensures forall x:R0 :: exp(x, 0.0) == 1.0
  {
    forall x:R0 ensures exp(x, 0.0) == 1.0
    {
      lem_exp_Pow0(x);
    }
  }

  // x^1 = x
  lemma lem_exp_Pow1(x:R0) 
    ensures exp(x, 1.0) == x
  { 
    lem_exp_One(x);
  }

  lemma lem_exp_Pow1Auto()
    ensures forall x:R0 :: exp(x, 1.0) == x
  {
    forall x:R0 ensures exp(x, 1.0) == x
    {
      lem_exp_Pow1(x);
    }
  }

  // x^2 = x*x
  lemma lem_exp_Pow2(x:R0) 
    ensures exp(x, 2.0) == x*x
  {  
    if x == 0.0 {
      lem_exp_BaseZero(2.0);
    } else {
      calc {
          exp(x, 2.0);
        == { lem_exp_Product(x, 1.0, 1.0); }
          exp(x, 1.0)*exp(x, 1.0);
        == { lem_exp_One(x); }
          x*x;
      } 
    }
  } 

  lemma lem_exp_Pow2Auto()
    ensures forall x:R0 :: exp(x, 2.0) == x*x
  {
    forall x:R0 ensures exp(x, 2.0) == x*x
    {
      lem_exp_Pow2(x);
    }
  }

  // x^3 = x*x*x
  lemma lem_exp_Pow3(x:R0) 
    ensures exp(x, 3.0) == x*x*x
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
    ensures forall x:R0 :: exp(x, 3.0) == x*x*x
  {
    forall x:R0 ensures exp(x, 3.0) == x*x*x
    {
      lem_exp_Pow3(x);
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
    else lem_exp_Positive(x, -y); 1.0 / exp(x, -y)
  }

  /******************************************************************************
    Order properties on the exponent with base >= 1 (or > 1)
  ******************************************************************************/

  // Strict increasing
  // b > 1 ∧ x < y ⟹ b^x < b^y
  lemma {:axiom} lem_exp_StrictIncr(b:R0, x:R0, y:R0)
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
    ensures forall b:R0, x:R0, y:R0 :: 
      b > 1.0 && x < y ==> exp(b, x) < exp(b, y)
  {
    forall b:R0, x:R0, y:R0 | b > 1.0
      ensures x < y ==> exp(b, x) < exp(b, y)
    {
      lem_exp_StrictIncr(b, x, y);
    }       
  }

  // Previous fact is reversible
  // b > 1 ∧ b^x < b^y ⟹ x < y
  lemma lem_exp_StrictIncrRev(b:R0, x:R0, y:R0)
    requires b > 1.0
    ensures  exp(b, x) < exp(b, y) ==> x < y
  { 
    var exp_b:real->real := (x => if x >= 0.0 then exp(b, x) else 0.0);
    assert forall x,y :: x >= 0.0 && x >= 0.0 && x < y ==> exp_b(x) < exp_b(y)
      by { lem_exp_StrictIncrAuto(); }
    lem_fun_StrictIncrIMPinjectivePred(exp_b, x => x >= 0.0);
    assert forall x,y :: x >= 0.0 && x >= 0.0 && exp_b(x) < exp_b(y) ==> x < y;
    assert forall x :: x >= 0.0 ==> exp_b(x) == exp(b, x);
  }

  lemma lem_exp_StrictIncrRevAuto()
    ensures forall b:R0, x:R0, y:R0 :: 
      b > 1.0 && exp(b, x) < exp(b, y) ==> x < y
  {
    forall b:R0, x:R0, y:R0 | b > 1.0
      ensures exp(b, x) < exp(b, y) ==> x < y
    {
      lem_exp_StrictIncrRev(b, x, y);
    }       
  }  

  // Join previous facts into an equivalence
  // b > 1 ⟹ (x < y ⟺ b^x < b^y)
  lemma lem_exp_StrictIncrIFF(b:R0, x:R0, y:R0)
    requires b > 1.0
    ensures  x < y <==> exp(b, x) < exp(b, y)
  { 
    lem_exp_StrictIncr(b,x,y);
    lem_exp_StrictIncrRev(b,x,y);
  }

  lemma lem_exp_StrictIncrIFFAuto()
    ensures forall b:R0, x:R0, y:R0 :: 
      b > 1.0 ==> (x < y <==> exp(b, x) < exp(b, y))
  {
    forall b:R0, x:R0, y:R0 | b > 1.0
      ensures x < y <==> exp(b, x) < exp(b, y)
    {
      lem_exp_StrictIncrIFF(b, x, y);
    }       
  }    

  // Weak version of lem_exp_StrictIncrIFF
  // b > 1 ⟹ (x <= y ⟺ b^x <= b^y)
  lemma lem_exp_MonoIncrIFF(b:R0, x:R0, y:R0)
    requires b > 1.0
    ensures  x <= y <==> exp(b, x) <= exp(b, y)
  {
    lem_exp_StrictIncrIFFAuto();
  }

  lemma lem_exp_MonoIncrIFFAuto()
    ensures forall b:R0, x:R0, y:R0 :: 
      b > 1.0 ==> (x <= y <==> exp(b, x) <= exp(b, y))
  {
    forall b:R0, x:R0, y:R0 | b > 1.0
      ensures x <= y <==> exp(b, x) <= exp(b, y)
    {
      lem_exp_MonoIncrIFF(b, x, y);
    }       
  }  

  // Weak version of lem_exp_StrictIncr, but also holds when x=1
  // b >= 1 ∧ x <= y ⟹ b^x <= b^y
  lemma lem_exp_MonoIncr(b:R0, x:R0, y:R0)
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
  lemma {:axiom} lem_exp_StrictDecr(b:R0, x:R0, y:R0)
    requires 0.0 < b < 1.0
    ensures x < y ==> exp(b, x) > exp(b, y) 

  lemma lem_exp_StrictDecrAuto()
    ensures forall b:R0, x:R0, y:R0 :: 
      0.0 < b < 1.0 && x < y ==> exp(b, x) > exp(b, y)
  {
    forall b:R0, x:R0, y:R0 | 0.0 < b < 1.0
      ensures x < y ==> exp(b, x) > exp(b, y)
    {
      lem_exp_StrictDecr(b, x, y);
    }       
  }

  // Previous fact is reversible
  // 0 < b < 1 ∧ b^x > b^y ⟹ x < y
  lemma lem_exp_StrictDecrRev(b:R0, x:R0, y:R0)
    requires 0.0 < b < 1.0
    ensures exp(b, x) > exp(b, y) ==> x < y
  {
    var exp_b:real->real := (x => if x >= 0.0 then exp(b, x) else 0.0);
    assert forall x,y :: x >= 0.0 && y >= 0.0 ==> (x < y ==> exp_b(x) > exp_b(y))
      by { lem_exp_StrictDecrAuto(); }
    lem_fun_StrictDecrIMPinjectivePred(exp_b, x => x >= 0.0);
    assert forall x,y :: x >= 0.0 && y >= 0.0 ==> (exp_b(x) > exp_b(y) ==> x < y);
    assert forall x :: x >= 0.0 ==> exp_b(x) == exp(b, x);       
  }   

  lemma lem_exp_StrictDecrRevAuto()
    ensures forall b:R0, x:R0, y:R0 :: 
      0.0 < b < 1.0 && exp(b, x) > exp(b, y) ==> x < y
  {
    forall b:R0, x:R0, y:R0 | 0.0 < b < 1.0
      ensures exp(b, x) > exp(b, y) ==> x < y
    {
      lem_exp_StrictDecrRev(b, x, y);
    }             
  }  

  // Join previous facts into an equivalence
  // 0 < b < 1 ⟹ (x < y ⟺ b^x > b^y)  
  lemma lem_exp_StrictDecrIFF(b:R0, x:R0, y:R0)
    requires 0.0 < b < 1.0
    ensures x < y <==> exp(b, x) > exp(b, y)
  {
    lem_exp_StrictDecr(b, x, y);
    lem_exp_StrictDecrRev(b, x, y);
  }

  lemma lem_exp_StrictDecrIFFAuto()
    ensures forall b:R0, x:R0, y:R0 :: 
      0.0 < b < 1.0 ==> (x < y <==> exp(b, x) > exp(b, y))
  {
    forall b:R0, x:R0, y:R0 | 0.0 < b < 1.0
      ensures x < y <==> exp(b, x) > exp(b, y)
    {
      lem_exp_StrictDecrIFF(b, x, y);
    }             
  }  

  // Weak version of lem_exp_StrictDecrIFF
  // 0 < b < 1 ⟹ (x <= y ⟺ b^x >= b^y) 
  lemma lem_exp_AntiMonoIncrIFF(b:R0, x:R0, y:R0)
    requires 0.0 < b < 1.0
    ensures x <= y <==> exp(b, x) >= exp(b, y)
  { 
    lem_exp_StrictDecrIFFAuto();
  }

  lemma lem_exp_AntiMonoIncrIFFAuto()
    ensures forall b:R0, x:R0, y:R0 :: 
      0.0 < b < 1.0 ==> (x <= y <==> exp(b, x) >= exp(b, y))
  {
    forall b:R0, x:R0, y:R0 | 0.0 < b < 1.0
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
    var exp_e:real->real := (x => if x >= 0.0 then exp(x, e) else 0.0);
    assert forall x,y :: x >= 0.0 && y >= 0.0 ==> (x < y ==> exp_e(x) < exp_e(y))
      by { lem_exp_BaseStrictIncrAuto(); } 
    lem_fun_StrictIncrIMPinjectivePred(exp_e, (x => x >= 0.0));
    assert forall x,y :: x >= 0.0 && y >= 0.0 ==> (exp_e(x) < exp_e(y) ==> x < y);
    assert forall x :: x >= 0.0 ==> exp_e(x) == exp(x, e);    
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
    ensures  N.exp(b, e) as R0 == exp(b as R0, e as R0)
  {
    if e == 0 {
      // BC: e = 0 
      calc {
           N.exp(b, 0) as R0;
        == { reveal N.exp(); }
           1.0;
        == { lem_exp_Zero(b as R0); }
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
        == { lem_exp_OverNat(b, e-1); }
           b as R0 * exp(b as R0, (e-1) as R0);  
        == { lem_exp_Def(b as R0, (e-1) as R0); }    
           exp(b as R0, e as R0);  
      }
    }
  }

  lemma lem_exp_OverNatAuto()
    ensures forall b:nat, e:nat :: 
      b > 0 ==> (N.exp(b, e) as R0 == exp(b as R0, e as R0))
  {
    forall b:nat, e:nat | b > 0
      ensures N.exp(b, e) as R0 == exp(b as R0, e as R0)
    {
      lem_exp_OverNat(b, e);
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
  lemma lem_exp2_StrictIncr(x:R0, y:R0)
    ensures x < y ==> exp2(x) < exp2(y)  
  {
    reveal exp2();
    lem_exp_StrictIncr(2.0, x, y);
  }

  // 2^x < 2^y ⟹ x < y
  lemma lem_exp2_StrictIncrRev(x:R0, y:R0)
    ensures exp2(x) < exp2(y) ==> x < y
  {
    reveal exp2();
    lem_exp_StrictIncrRev(2.0, x, y);
  }  

  // x < y ⟺ 2^x < 2^y 
  lemma lem_exp2_StrictIncrIFF(x:R0, y:R0)
    ensures x < y <==> exp2(x) < exp2(y) 
  {
    reveal exp2();
    lem_exp_StrictIncrIFF(2.0, x, y);
  }    

  // x <= y ⟹ 2^x <= 2^y
  lemma lem_exp2_MonoIncr(x:R0, y:R0)
    ensures x <= y ==> exp2(x) <= exp2(y)  
  {
    lem_exp2_StrictIncr(x, y);
  }

}