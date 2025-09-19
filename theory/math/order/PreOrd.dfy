/******************************************************************************
  PreOrder structure (T,<=)
******************************************************************************/

// In a preorder there is no guaranteed link between ≤ and =
// We could have x ≠ y and x <= y and y <= x.
// Note: = (equality) is handled by Dafny

abstract module PreOrd {

  type T

  // x <= y
  ghost predicate Leq(x:T, y:T)  

  // x >= y
  ghost predicate Geq(x:T, y:T) { Leq(y, x) }

  // Reflexivity
  // x <= x
  lemma {:axiom} lem_Leq_Refl(x:T)
    ensures Leq(x, x)

  lemma lem_Leq_ReflAuto()
    ensures forall x:T :: Leq(x, x)
  {
    forall x:T ensures Leq(x, x)
    {
      lem_Leq_Refl(x);
    }
  }  

  // Transitivity
  // x <= y ∧ y <= z ⟹ x <= z
  lemma {:axiom} lem_Leq_Trans(x:T, y:T, z:T)
    requires Leq(x, y) && Leq(y, z)
    ensures  Leq(x, z)

  lemma lem_Leq_TransAuto()
    ensures forall x,y,z:T :: Leq(x, y) && Leq(y, z) ==> Leq(x, z)
  {
    forall x,y,z:T | Leq(x, y) && Leq(y, z) 
      ensures Leq(x, z) 
    {
      lem_Leq_Trans(x, y, z);
    }
  }  

  /******************************************************************************
    Connect <= with =
  ******************************************************************************/ 

  // x = y ⟹ x <= z
  lemma {:axiom} lem_Leq_SubstEq(x:T, y:T)
    requires x == y
    ensures  Leq(x, y)

  lemma lem_Leq_SubstEqAuto()
    ensures forall x,y:T :: x == y ==> Leq(x, y)
  {
    forall x,y:T | x == y
      ensures Leq(x, y)
    {
      lem_Leq_SubstEq(x, y);
    }
  } 

  // x = y ∧ y <= z ⟹ x <= z
  lemma lem_Leq_SubstEqLeft(x:T, y:T, z:T)
    requires x == y && Leq(y, z)
    ensures  Leq(x, z)
  { }

  // x <= y ∧ y = z ⟹ x <= z
  lemma lem_Leq_SubstEqRight(x:T, y:T, z:T)
    requires Leq(x, y) && y == z
    ensures  Leq(x, z)
  { }

  /******************************************************************************
    Strict version (T,<)
  ******************************************************************************/  

  // x < y ⟺ x <= y ∧ x ≠ y
  ghost predicate Lt(x:T, y:T) { Leq(x, y) && x != y }

  // Irreflexivity
  // ! (x < x)
  lemma lem_Lt_Irrefl(x:T)
    ensures !Lt(x, x)
  { }  

  // x = y ∧ y < z ⟹ x < z
  lemma lem_Lt_SubstEqLeft(x:T, y:T, z:T)
    requires x == y && Lt(y, z)
    ensures  Lt(x, z)
  { }

  // x < y ∧ y = z ⟹ x < z
  lemma lem_Lt_SubstEqRight(x:T, y:T, z:T)
    requires Lt(x, y) && y == z
    ensures  Lt(x, z)
  { }

}