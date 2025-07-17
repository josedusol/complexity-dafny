
/**************************************************************************
  Exponentiation over reals
**************************************************************************/

module ExpReal {

  ghost function {:axiom} exp(x:real, y:real) : real
    ensures x >= 0.0 && y >= 0.0 ==> exp(x, y) >= 0.0  

  lemma {:axiom} lem_expZeroZero()
    ensures exp(0.0, 0.0) == 1.0 

  lemma {:axiom} lem_expZero(x:real)
    requires x > 0.0
    ensures exp(x, 0.0) == 1.0 

  lemma {:axiom} lem_expOne(x:real)
    requires x > 0.0
    ensures exp(x, 1.0) == x

  lemma {:axiom} lem_expProduct(x:real, y:real, z:real)
    requires x > 0.0 
    ensures exp(x, y+z) == exp(x, y)*exp(x, z)  

  // b >= 1 /\ x <= y ==> b^x <= b^y
  lemma {:axiom} lem_expMono(b:real, x:real, y:real)
    requires b >= 1.0
    ensures  x <= y ==> exp(b, x) <= exp(b, y)

  // e,x,y >= 0 /\ x <= y ==> x^e <= y^e
  lemma {:axiom} lem_expBaseMono(e:real, x:real, y:real)
    requires e >= 0.0 && x >= 0.0 && y >= 0.0
    ensures  x <= y ==> exp(x, e) <= exp(y, e)

  lemma {:axiom} lem_expZeroAll()
    ensures forall x:real :: x > 0.0 ==> exp(x, 0.0) == 1.0 

  lemma {:axiom} lem_expOneAll()
    ensures forall x:real :: x > 0.0 ==> exp(x, 1.0) == x  

  lemma {:axiom} lem_expProductAll()
    ensures forall x:real, y:real, z:real :: 
            x > 0.0 ==> exp(x, y+z) == exp(x, y)*exp(x, z)

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

  lemma lem_expTwoAll()
    ensures forall x:real :: x > 0.0 ==> exp(x, 2.0) == x*x
  {
    forall x:real | x > 0.0
      ensures exp(x, 2.0) == x*x
    {
      lem_expTwo(x);
    }
  }

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