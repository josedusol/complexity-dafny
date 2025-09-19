include "../Logic.dfy"
include "./PartialOrd.dfy"

/******************************************************************************
  Total Order structure (T,<=)
******************************************************************************/

abstract module TotalOrd refines PartialOrd {

  import opened Logic

  // x ≠ y ⟹ x < y ∨ y < x
  lemma {:axiom} lem_Leq_Comparable(x:T, y:T)
    requires x != y
    ensures  Lt(x, y) || Lt(y, x)

  /******************************************************************************
    Strict version (T,<)
  ******************************************************************************/  

  // Only one of x = y, x < y or y < x holds
  lemma lem_Lt_Trichotomy(x:T, y:T)
    ensures xor3(x == y, Lt(x, y), Lt(y, x))
  { 
    // First prove the disjunction
    assert x == y || Lt(x, y) || Lt(y, x) by {
      // By RAA, suppose the opposite
      if !(x == y || Lt(x, y) || Lt(y, x)) {
        assert !Lt(x, y) && !Lt(y, x);
        assert Lt(x, y) || Lt(y, x) by {  assert x != y; lem_Leq_Comparable(x, y); }
        assert false;
      } 
    }
    // Now establish mutual exclusivity
    if x == y {
      assert !Lt(x, y);
      assert !Lt(y, x);
    }
    else if Lt(x, y) {
      assert x != y;
      assert !Lt(y, x) by { lem_Lt_Asym(x, y); }
    }    
    else if Lt(y, x) {
      assert x != y;
      assert !Lt(x, y) by { lem_Lt_Asym(y, x); }
    }   
  }

}