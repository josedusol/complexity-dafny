include "./ExpReal.dfy"
include "./Root2Nat.dfy"

/******************************************************************************
  Roots over non-negative reals
******************************************************************************/

module RootReal {

  import Exp = ExpReal
  //import N = Root2Nat

  // ᵏ√x = x^(1/k)
  opaque ghost function root(x:real, k:real) : real
    requires x >= 0.0 && k > 0.0
  {
    Exp.exp(x, 1.0 / k)
  }

  // Non-negativity
  // x >= 0 ∧ k > 0 ⟹ ᵏ√x >= 0
  lemma lem_NonNegative(x:real, k:real)
    requires x >= 0.0 && k > 0.0 
    ensures root(x, k) >= 0.0
  { 
    reveal root();  
  }

  lemma lem_NonNegativeAuto()
    ensures forall x, k :: x >= 0.0 && k > 0.0 ==> root(x, k) >= 0.0
  { 
     forall x:real, k:real | x >= 0.0 && k > 0.0
      ensures root(x, k) >= 0.0
    {
      lem_NonNegative(x, k);
    }
  }

  // k > 0 ⟹  ᵏ√0 = 0
  lemma lem_Zero(k:real)
    requires k > 0.0
    ensures  root(0.0, k) == 0.0 
  {
    reveal root();
    Exp.lem_BaseZero(1.0/k);
  } 

  // Identity for 1st root
  // ¹√x = x
  lemma lem_Identity(x:real)
    requires x >= 0.0
    ensures root(x, 1.0) == x
  {
    reveal root();
    Exp.lem_One(x);
  }

  /******************************************************************************
    ᵏ√x and power x^k are inverses of each other for x ∈ (0,∞)
  ******************************************************************************/

  // ᵏ√(x^k) = x 
  lemma lem_RootPowInverse(x:real, k:real)
    requires x > 0.0 && k > 0.0
    ensures  root(Exp.exp(x, k), k) == x 
  {
    ghost var r := 1.0/k;
    calc {
         root(Exp.exp(x, k), k);
      == { reveal root(); }
         Exp.exp(Exp.exp(x, k), r);
      == { Exp.lem_Exp(x, k, r); }    
         Exp.exp(x, k*r); 
      == { assert k*r == k*(1.0/k) == 1.0; }
         Exp.exp(x, 1.0); 
      == { Exp.lem_One(x); }
         x;    
    }
  }

  // (ᵏ√x)^k = x 
  lemma lem_PowRootInverse(x:real, k:real)
    requires x > 0.0 && k > 0.0
    ensures  Exp.exp(root(x, k), k) == x
  {
    ghost var r := 1.0/k;
    calc { 
         Exp.exp(root(x, k), k);
      == { reveal root(); }
         Exp.exp(Exp.exp(x, r), k);
      == { Exp.lem_Exp(x, r, k); }
         Exp.exp(x, r*k);
      == { assert k*r == k*(1.0/k) == 1.0; }
         Exp.exp(x, 1.0);
      == { Exp.lem_One(x); }
         x;   
    }
  }  

  /******************************************************************************
    Order properties on the radicand
  ******************************************************************************/

  // ᵏ√x is strictly increasing in the radicand x ∈ [0,∞)
  // k > 0 ∧ x,y >= 0 ∧ x < y ⟹ ᵏ√x < ᵏ√y
  lemma lem_RadStrictIncr(x:real, y:real, k:real)
    requires k > 0.0 && x >= 0.0 && y >= 0.0
    ensures x < y ==> root(x, k) < root(y, k)
  {
    reveal root();
    Exp.lem_BaseStrictIncr(1.0 / k, x, y);
  }

  // TODO: derive related properties

  /******************************************************************************
    Order properties on the index when the radicand x ∈ (0,1)
  ******************************************************************************/  

  // ᵏ√x is strictly increasing in the index
  // 0 < x < 1 ∧ k,h > 0 ∧ k < h ⟹ ᵏ√x < ʰ√x
  lemma lem_IndexStrictIncr(x:real, k:real, h:real)
    requires 0.0 < x < 1.0 && k > 0.0 && h > 0.0
    ensures k < h ==> root(x, k) < root(x, h)
  {
    reveal root();
    Exp.lem_StrictDecr(x, 1.0 / h, 1.0 / k);
    assert 1.0/h < 1.0/k ==> Exp.exp(x,1.0/h) > Exp.exp(x,1.0/k);
  }

  // TODO: derive related properties
  
  /******************************************************************************
    Order properties on the index when the radicand x=0 or x>=1 
  ******************************************************************************/    

  // ᵏ√x is strictly decreasing in the index when x > 1 
  // x > 1 ∧ k,h > 0 ∧ k < h ⟹ ᵏ√x > ʰ√x
  lemma lem_IndexStrictDecr(x:real, k:real, h:real)
    requires x > 1.0 && k > 0.0 && h > 0.0 
    ensures k < h ==> root(x, k) > root(x, h)
  {
    reveal root();
    Exp.lem_StrictIncr(x, 1.0 / h, 1.0 / k);
    assert 1.0/h < 1.0/k ==> Exp.exp(x,1.0/h) < Exp.exp(x,1.0/k);
  }

  // A weak version of lem_IndexStrictDecr but holds for x=0 and x=1
  // (x = 0 ∨ x >= 1) ∧ k,h > 0 ∧ k <= h ⟹ ᵏ√x >= ʰ√x
  lemma lem_IndexMonoDecr(x:real, k:real, h:real)
    requires x == 0.0 || x >= 1.0 
    requires k > 0.0 && h > 0.0
    ensures  k <= h ==> root(x, k) >= root(x, h)
  {
    if x == 0.0 {
      lem_Zero(k);
      lem_Zero(h);
    } else if x >= 1.0 {
      reveal root();
      Exp.lem_MonoIncr(x, 1.0 / h, 1.0 / k);
      assert 1.0/h <= 1.0/k ==> Exp.exp(x,1.0/h) <= Exp.exp(x,1.0/h);
    }
  }

  // Bound the real-valued √ function with the natural-number version N.√

}