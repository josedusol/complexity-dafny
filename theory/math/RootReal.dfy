include "./ExpReal.dfy"
include "./Root2Nat.dfy"

/******************************************************************************
  Roots over over non-negative reals
******************************************************************************/

module RootReal {

  import opened ExpReal
  import N = Root2Nat

  // root(x,q) = x^(1/q)
  opaque ghost function root(x:real, q:real) : real
    requires x >= 0.0 && q > 0.0
  {
    exp(x, 1.0 / q)
  }

  // Non-negativity
  // x >= 0 ∧ q > 0 ⇒ root(x,q) >= 0
  lemma lem_root_NonNegative(x:real, q:real)
    requires x >= 0.0 && q > 0.0 
    ensures root(x, q) >= 0.0
  { 
    reveal root();  
  }

  // q > 0 ⇒ root(0,q) = 0
  lemma lem_root_Zero(q:real)
    requires q > 0.0
    ensures  root(0.0, q) == 0.0 
  {
    reveal root();
    lem_exp_BaseZero(1.0/q);
  } 

  // Identity for 1st root
  // root(x,1) = x
  lemma lem_root_Identity(x:real)
    requires x >= 0.0
    ensures root(x, 1.0) == x
  {
    reveal root();
    lem_exp_One(x);
  }

  /******************************************************************************
    root(x,q) and power x^q are inverses of each other for x ∈ (0,∞)
  ******************************************************************************/

  opaque ghost function nam(q:real):real
    requires q > 0.0
  {
    1.0/q
  }

  // root(x^q,q) = x 
  lemma lem_rootPow_Inverse(x:real, q:real)
    requires x > 0.0 && q > 0.0
    ensures  root(exp(x, q), q) == x 
  {
    ghost var r := 1.0/q;
    calc {
         root(exp(x, q), q);
      == { reveal root(); }
         exp(exp(x, q), r);
      == { lem_exp_Exp(x, q, r); }    
         exp(x, q*r); 
      == { assert q*r == q*(1.0/q) == 1.0; }
         exp(x, 1.0); 
      == { lem_exp_One(x); }
         x;    
    }
  }

  // root(x,q)^q = x 
  lemma lem_PowRoot_Inverse(x:real, q:real)
    requires x > 0.0 && q > 0.0
    ensures  exp(root(x, q), q) == x
  {
    ghost var r := 1.0/q;
    calc { 
         exp(root(x, q), q);
      == { reveal root(); }
         exp(exp(x, r), q);
      == { lem_exp_Exp(x, r, q); }
         exp(x, r*q);
      == { assert q*r == q*(1.0/q) == 1.0; }
         exp(x, 1.0); 
      == { lem_exp_One(x); }
         x;   
    }
  }  

  /******************************************************************************
    Order properties on the radicand
  ******************************************************************************/

  // root(x,q) is strictly increasing in the radicand x ∈ [0,∞)
  // x,y >= 0 ∧ x < y ⇒ root(x,q) < root(y,q)
  lemma lem_root_RadStrictIncr(x:real, y:real, q:real)
    requires x >= 0.0 && y >= 0.0 && q > 0.0
    ensures x < y ==> root(x, q) < root(y, q)
  {
    reveal root();
    lem_exp_BaseStrictIncr(1.0 / q, x, y);
  }

  // TODO: derive related properties

  /******************************************************************************
    Order properties on the index when the radicand x ∈ (0,1)
  ******************************************************************************/  

  // root(x,q) is strictly increasing in the index
  // 0 < x < 1 ∧ p,q > 0 ∧ p < q ⇒ root(x,p) < root(x,q)
  lemma lem_root_IndexStrictIncr(x:real, p:real, q:real)
    requires 0.0 < x < 1.0 && p > 0.0 && q > 0.0
    ensures p < q ==> root(x, p) < root(x, q)
  {
    reveal root();
    lem_exp_StrictDecr(x, 1.0 / q, 1.0 / p);
    assert 1.0/q < 1.0/p ==> exp(x,1.0/q) > exp(x,1.0/p);
  }

  // TODO: derive related properties
  
  /******************************************************************************
    Order properties on the index when the radicand x=0 or x>=1 
  ******************************************************************************/    

  // root(x,q) is strictly decreasing in the index when x > 1 
  // x > 1 ∧ p,q > 0 ∧ p < q ⇒ root(x,p) > root(x,q)
  lemma lem_root_IndexStrictDecr(x:real, p:real, q:real)
    requires x > 1.0 && p > 0.0 && q > 0.0 
    ensures p < q ==> root(x, p) > root(x, q)
  {
    reveal root();
    lem_exp_StrictIncr(x, 1.0 / q, 1.0 / p);
    assert 1.0/q < 1.0/p ==> exp(x,1.0/q) < exp(x,1.0/p);
  }

  // A weak version of lem_root_IndexStrictDecr but holds for x=0 and x=1
  // (x = 0 ∨ x >= 1) ∧ p,q > 0 ∧ p <= q ⇒ root(x,p) >= root(x,q)
  lemma lem_root_IndexMonoDecr(x:real, p:real, q:real)
    requires x == 0.0 || x >= 1.0 
    requires p > 0.0 && q > 0.0
    ensures p <= q ==> root(x, p) >= root(x, q)
  {
    if x == 0.0 {
      lem_root_Zero(p);
      lem_root_Zero(q);
    } else if x >= 1.0 {
      reveal root();
      lem_exp_MonoIncr(x, 1.0 / q, 1.0 / p);
      assert 1.0/q <= 1.0/p ==> exp(x,1.0/q) <= exp(x,1.0/p);
    }
  }

  // Bound the real-valued sqrt function with the natural-number version N.sqrt

}