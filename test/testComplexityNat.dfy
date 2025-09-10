include "../theory/math/ExpNat.dfy"
include "../theory/math/LemBoundsNat.dfy"
include "../theory/math/LemFunction.dfy"
include "../theory/math/Log2Nat.dfy"
include "../theory/math/SumInt.dfy"
include "../theory/ComplexityNat.dfy"
include "../theory/LemComplexityNat.dfy"

import opened ExpNat
import opened LemBoundsNat
import opened LemFunction
import opened Log2Nat
import opened SumInt
import opened ComplexityNat
import opened LemComplexityNat

lemma test_bigOprod()
  requires ((n:nat) => 2*n) in O(linGrowth())
  requires ((n:nat) => 3*n) in O(linGrowth())
  ensures  ((n:nat) => (2*n)*(3*n)) in O(quadGrowth())
{
  var f1:nat->nat := n => 2*n;
  var f2:nat->nat := n => 3*n;

  lem_bigO_prod(f1, linGrowth(), f2, linGrowth());  
  assert ((n:nat) => f1(n)*f2(n)) in O(n => linGrowth()(n)*linGrowth()(n));

  lem_fun_Ext((n:nat) => linGrowth()(n)*linGrowth()(n), quadGrowth())
    by { assert forall n:nat :: linGrowth()(n)*linGrowth()(n) == quadGrowth()(n) 
           by { lem_exp_Pow1Auto(); lem_exp_Pow2Auto(); }
    } 
  lem_fun_Ext((n:nat) => f1(n)*f2(n), (n:nat) => (2*n)*(3*n)); 
}

lemma test_polyBigO() returns (c:nat, n0:nat)
  ensures ((n:nat) => 3*exp(n,2) + 100*exp(n,1) + 10) in O(quadGrowth())
{
  var poly := n => 3*exp(n,2) + 100*exp(n,1) + 10;

  c, n0 := 113, 1;
  forall n:nat | 0 <= n0 <= n
    ensures poly(n) <= c*quadGrowth()(n)
  {
    calc {
         poly(n);
      == 3*exp(n,2) + 100*exp(n,1) + 10;
      <= { reveal exp(); }
         c*exp(n,2); 
    }
    assert poly(n) <= c*quadGrowth()(n);
  }
  assert bigOfrom(c, n0, poly, quadGrowth());
} 

lemma test_log2BigOlin() returns (c:nat, n0:nat)
  ensures ((n:nat) => log2(n+1)) in O(linGrowth())
{
  c, n0 := 1, 1;
  forall n:nat | 0 <= n0 <= n
    ensures log2(n+1) <= c*linGrowth()(n)
  {
    calc {
         log2(n+1);
      <= { lem_log2nPlus1LEQn(n); }
         n;
      == { reveal exp(); }
         c*exp(n,1);  
    }
    assert log2(n+1) <= c*linGrowth()(n);
  }
  assert bigOfrom(c, n0, n => log2(n+1), linGrowth());
} 