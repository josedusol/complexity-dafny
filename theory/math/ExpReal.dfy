include "./ExpNat.dfy"

/******************************************************************************
  Exponentiation over reals
******************************************************************************/

module ExpReal {
  import N = ExpNat

  // x^y
  // We assert lem_expIsNonNegative as post for convenience
  ghost function {:axiom} exp(x:real, y:real) : real
    ensures x >= 0.0 && y >= 0.0 ==> exp(x, y) >= 0.0

  // x,y >= 0 ==> x^y >= 0
  lemma {:axiom} lem_expIsNonNegative(x:real, y:real)
    requires x >= 0.0 && y >= 0.0
    ensures  exp(x, y) >= 0.0

  // x > 0 /\ y >= 0 ==> x^y > 0
  lemma {:axiom} lem_expIsPositive(x:real, y:real)
    requires x > 0.0 && y >= 0.0
    ensures  exp(x, y) > 0.0  

  // x >= 1 /\ y >= 0 ==> x^y >= 1
  lemma {:axiom} lem_expGEQone(x:real, y:real)
    requires x >= 1.0 && y >= 0.0
    ensures  exp(x, y) >= 1.0        

  // // 0^0 = 1   do we need this?
  // lemma {:axiom} lem_expZeroZero()
  //   ensures exp(0.0, 0.0) == 1.0 

  // y > 0 ==> 0^y = 0
  lemma {:axiom} lem_expBaseZero(y:real)
    requires y > 0.0
    ensures  exp(0.0, y) == 0.0     

  // x > 0 ==> x^0 = 1
  lemma {:axiom} lem_expZero(x:real)
    requires x > 0.0
    ensures  exp(x, 0.0) == 1.0 

  // x > 0 ==> x^1 = x
  lemma {:axiom} lem_expOne(x:real)
    requires x > 0.0
    ensures  exp(x, 1.0) == x

  // x > 0 ==> x^(y+z) = (x^y)*(x^z)
  lemma {:axiom} lem_expProduct(x:real, y:real, z:real)
    requires x > 0.0 
    ensures  exp(x, y+z) == exp(x, y)*exp(x, z)  

  // b >= 1 /\ x <= y ==> b^x <= b^y
  lemma {:axiom} lem_expMonoIncr(b:real, x:real, y:real)
    requires b >= 1.0
    ensures  x <= y ==> exp(b, x) <= exp(b, y)

  // e,x,y >= 0 /\ x <= y ==> x^e <= y^e
  lemma {:axiom} lem_expBaseMonoIncr(e:real, x:real, y:real)
    requires e >= 0.0 && x >= 0.0 && y >= 0.0
    ensures  x <= y ==> exp(x, e) <= exp(y, e)

  // x > 0 ==> x*x^y = x^(y+1)
  lemma lem_expDef(x:real, y:real)
    requires x > 0.0 
    ensures  x*exp(x, y) == exp(x, y + 1.0)
  { 
    calc {
         x*exp(x, y);
      == { lem_expOne(x); }
         exp(x, 1.0)*exp(x, y);
      == { lem_expProduct(x, 1.0, y); }
         exp(x, y + 1.0);
    } 
  } 

  // x > 0 ==> x^2 = x*x
  lemma lem_expTwo(x:real) 
    requires x > 0.0
    ensures  exp(x, 2.0) == x*x
  {  
    calc {
        exp(x, 2.0);
      == { lem_expProduct(x, 1.0, 1.0); }
        exp(x, 1.0)*exp(x, 1.0);
      == { lem_expOne(x); }
        x*x;
    } 
  } 

  // Tie the real-valued exp function to the natural-number version N.exp
  // under overlapping domains
  lemma lem_expOverNat(b:nat, e:nat)
    requires b > 0
    ensures  N.exp(b, e) as real == exp(b as real, e as real)
  {
    if e == 0 {
      // BC: e = 0 
      calc {
           N.exp(b, 0) as real;
        == { reveal N.exp(); }
           1.0;
        == { lem_expZero(b as real); }
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
        == { lem_expOverNat(b, e-1); }
           b as real * exp(b as real, (e-1) as real);  
        == { lem_expDef(b as real, (e-1) as real); }    
           exp(b as real, e as real);  
      }
    }
  }

  /******************************************************************************
    Special 2^x
  ******************************************************************************/

  // 2^x
  ghost function exp2(y:real) : real
  { 
    exp(2.0, y)
  }

  /******************************************************************************
    Universal closures of lemmas
  ******************************************************************************/

  // x,y >= 0 ==> x^y >= 0
  lemma lem_expIsNonNegativeAll()
    ensures forall x:real, y:real ::  
            x >= 0.0 && y >= 0.0 ==> exp(x, y) >= 0.0
  {
     forall x:real, y:real | x >= 0.0 && y >= 0.0
      ensures exp(x, y) >= 0.0
    {
      lem_expIsNonNegative(x, y);
    }
  }

  // x > 0, y >= 0 ==> x^y > 0
  lemma lem_expIsPositiveAll()
    ensures forall x:real, y:real ::  
            x > 0.0 && y >= 0.0 ==> exp(x, y) > 0.0
  {
     forall x:real, y:real | x > 0.0 && y >= 0.0
      ensures exp(x, y) > 0.0
    {
      lem_expIsPositive(x, y);
    }
  }  

  lemma lem_expZeroAll()
    ensures forall x:real :: x > 0.0 ==> exp(x, 0.0) == 1.0 
  {
    forall x:real | x > 0.0
      ensures exp(x, 0.0) == 1.0 
    {
      lem_expZero(x);
    }
  }

  lemma lem_expOneAll()
    ensures forall x:real :: x > 0.0 ==> exp(x, 1.0) == x 
  {
    forall x:real | x > 0.0
      ensures exp(x, 1.0) == x 
    {
      lem_expOne(x);
    }    
  }

  lemma lem_expProductAll()
    ensures forall x:real, y:real, z:real :: 
            x > 0.0 ==> exp(x, y+z) == exp(x, y)*exp(x, z)
  {
    forall x:real, y:real, z:real | x > 0.0
      ensures exp(x, y+z) == exp(x, y)*exp(x, z)
    {
      lem_expProduct(x, y, z);
    }   
  }

  lemma lem_expTwoAll()
    ensures forall x:real :: x > 0.0 ==> exp(x, 2.0) == x*x
  {
    forall x:real | x > 0.0
      ensures exp(x, 2.0) == x*x
    {
      lem_expTwo(x);
    }
  }

  lemma lem_expDefAll()
    ensures forall x:real, y:real :: 
            x > 0.0 ==> x*exp(x, y) == exp(x, y + 1.0)
  {
    forall x:real, y:real | x > 0.0
      ensures x*exp(x, y) == exp(x, y + 1.0)
    {
      lem_expDef(x, y);
    }
  }

}