
/**************************************************************************
  Power over non-negative integers
**************************************************************************/

module ExpReal {

  ghost function {:axiom} pow(x:real, y:real) : real
    ensures x >= 0.0 && y >= 0.0 ==> pow(x, y) >= 0.0  

  lemma {:axiom} lem_powZeroZero() // assume 0.0^0.0 = 1
    ensures pow(0.0, 0.0) == 1.0 

  lemma {:axiom} lem_powZero(x:real)
    requires x > 0.0
    ensures pow(x, 0.0) == 1.0 

  lemma {:axiom} lem_powOne(x:real)
    requires x > 0.0
    ensures pow(x, 1.0) == x

  lemma {:axiom} lem_powProduct(x:real, y:real, z:real)
    requires x > 0.0 
    ensures pow(x, y+z) == pow(x, y)*pow(x, z)  

  lemma {:axiom} lem_powZeroAll()
    ensures forall x:real :: x > 0.0 ==> pow(x, 0.0) == 1.0 

  lemma {:axiom} lem_powOneAll()
    ensures forall x:real :: x > 0.0 ==> pow(x, 1.0) == x  

  lemma {:axiom} lem_powProductAll()
    ensures forall x:real, y:real, z:real :: 
            x > 0.0 ==> pow(x, y+z) == pow(x, y)*pow(x, z)

  lemma lem_powTwo(x:real) 
    requires x > 0.0
    ensures  pow(x, 2.0) == x*x
  {  
    calc {
        pow(x, 2.0);
      == { lem_powProduct(x, 1.0, 1.0); }
        pow(x, 1.0)*pow(x, 1.0);
      == { lem_powOne(x); }
        x*x;
    } 
  } 

  lemma lem_powTwoAll()
    ensures forall x:real :: x > 0.0 ==> pow(x, 2.0) == x*x
  {
    forall x:real | x > 0.0
      ensures pow(x, 2.0) == x*x
    {
      lem_powTwo(x);
    }
  }

  lemma lem_powDef(x:real, y:real)
    requires x > 0.0 
    ensures  x*pow(x, y) == pow(x, y + 1.0)
  { 
    calc {
        x*pow(x, y);
      == { lem_powOne(x); }
        pow(x, 1.0)*pow(x, y);
      == { lem_powProduct(x, 1.0, y); }
        pow(x, y + 1.0);
    } 
  } 

  lemma lem_powDefAll()
    ensures forall x:real, y:real :: 
            x > 0.0 ==> x*pow(x, y) == pow(x, y + 1.0)
  {
    forall x:real, y:real | x > 0.0
      ensures x*pow(x, y) == pow(x, y + 1.0)
    {
      lem_powDef(x, y);
    }
  }

}