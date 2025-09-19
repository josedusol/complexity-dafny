include "./PreOrd.dfy"

/******************************************************************************
  Partial Order structure (T,<=)
******************************************************************************/

abstract module PartialOrd refines PreOrd {

  // AntiSymmetry
  // x <= y ∧ y <= x ⟹ x = y
  lemma {:axiom} lem_Leq_AntiSym(x:T, y:T)
    requires Leq(x, y) && Leq(y, x)
    ensures x == y

  /******************************************************************************
    Strict version (T,<)
  ******************************************************************************/  

  // Transitivity
  // x < y ∧ y < z ⟹ x < z
  lemma lem_Lt_Trans(x:T, y:T, z:T)
    requires Lt(x, y) && Lt(y, z)
    ensures  Lt(x, z)
  { 
    assert Leq(x, z) by { lem_Leq_Trans(x, y, z); }
    assert x != z by {
      // By RAA, suppose x == z
      if x == z {
        assert x != y;
        assert x == y 
          by { assert Leq(x, y) && Leq(y, x); lem_Leq_AntiSym(x, y); }
        assert false;
      }  
    }
  }

  lemma lem_Lt_TransAuto()
    ensures forall x,y,z:T :: Lt(x, y) && Lt(y, z) ==> Lt(x, z)
  {
    forall x,y,z:T | Lt(x, y) && Lt(y, z) 
      ensures Lt(x, z) 
    {
      lem_Lt_Trans(x, y, z);
    }
  }  

  // Asymmetry
  // x < y ⟹ !(y < z)
  lemma lem_Lt_Asym(x:T, y:T)
    requires Lt(x, y)
    ensures  !Lt(y, x)
  { 
    assert !Leq(y, x) by {
      // By RAA, suppose y <= x
      if Leq(y, x) {
        assert x != y;
        assert x == y 
          by { assert Leq(x, y) && Leq(y, x); lem_Leq_AntiSym(x, y); }
        assert false;
      }
    }
  }

  lemma lem_Lt_AsymAuto()
    ensures forall x,y:T :: Lt(x, y) ==> !Lt(y, x)
  {
    forall x,y:T | Lt(x, y)
      ensures !Lt(y, x)
    {
      lem_Lt_Asym(x, y);
    }
  } 

}