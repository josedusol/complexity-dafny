
/**************************************************************************
  Power over non-negative integers
**************************************************************************/

module ExpReal {

  ghost function {:axiom} powr(x:real, y:real) : real
    ensures x >= 0.0 && y >= 0.0 ==> powr(x, y) >= 0.0  

  lemma {:axiom} lem_powrZeroZero() // assume 0.0^0.0 = 1
    ensures  powr(0.0, 0.0) == 1.0 

  lemma {:axiom} lem_powrZero(x:real)
    requires x > 0.0
    ensures  powr(x, 0.0) == 1.0 

  lemma {:axiom} lem_powrOne(x:real)
    requires x > 0.0
    ensures  powr(x, 1.0) == x

  lemma {:axiom} lem_powrProduct(x:real, y:real, z:real)
    requires x > 0.0 
    ensures powr(x, y+z) == powr(x, y)*powr(x, z)  

  lemma {:axiom} lem_powrZeroAll()
    ensures forall x:real :: x > 0.0 ==> powr(x, 0.0) == 1.0 

  lemma {:axiom} lem_powrOneAll()
    ensures forall x:real :: x > 0.0 ==> powr(x, 1.0) == x  

  lemma {:axiom} lem_powrProductAll()
    ensures forall x:real, y:real, z:real :: 
            x > 0.0 ==> powr(x, y+z) == powr(x, y)*powr(x, z)

  lemma lem_powrTwo(x:real) 
    requires x > 0.0
    ensures  powr(x, 2.0) == x*x
  {  
    calc {
        powr(x, 2.0);
      == { lem_powrProduct(x, 1.0, 1.0); }
        powr(x, 1.0)*powr(x, 1.0);
      == { lem_powrOne(x); }
        x*x;
    } 
  } 

  lemma lem_powrTwoAll()
    ensures forall x:real :: x > 0.0 ==> powr(x, 2.0) == x*x
  {
    forall x:real | x > 0.0
      ensures powr(x, 2.0) == x*x
    {
      lem_powrTwo(x);
    }
  }

  lemma lem_powrDef(x:real, y:real)
    requires x > 0.0 
    ensures  x*powr(x, y) == powr(x, y + 1.0)
  { 
    calc {
        x*powr(x, y);
      == { lem_powrOne(x); }
        powr(x, 1.0)*powr(x, y);
      == { lem_powrProduct(x, 1.0, y); }
        powr(x, y + 1.0);
    } 
  } 

  lemma lem_powrDefAll()
    ensures forall x:real, y:real :: 
            x > 0.0 ==> x*powr(x, y) == powr(x, y + 1.0)
  {
    forall x:real, y:real | x > 0.0
      ensures x*powr(x, y) == powr(x, y + 1.0)
    {
      lem_powrDef(x, y);
    }
  }

}