include "../theory/math/ExpNat.dfy"
include "../theory/math/LemBoundsNat.dfy"
include "../theory/math/LemFunction.dfy"
include "../theory/math/LogNat.dfy"
include "../theory/math/SumInt.dfy"
include "../theory/ComplexityNat.dfy"
include "../theory/LemComplexityNat.dfy"

import opened ExpNat
import opened LemBoundsNat
import opened LemFunction
import opened LogNat
import opened SumInt
import opened ComplexityNat
import opened LemComplexityNat

lemma test_bigOprod()
  requires bigO(n => 2*n, linGrowth())
  requires bigO(n => 3*n, linGrowth())
  ensures  bigO(n => (2*n)*(3*n), quadGrowth())
{
  var f1:nat->nat := n => 2*n; 
  var f2:nat->nat := n => 3*n;

  lem_bigO_prod(f1, linGrowth(), f2, linGrowth());  
  assert bigO((n:nat) => f1(n)*f2(n), n => linGrowth()(n)*linGrowth()(n));

  lem_funExt((n:nat) => linGrowth()(n)*linGrowth()(n), quadGrowth())
    by { assert forall n:nat :: linGrowth()(n)*linGrowth()(n) == quadGrowth()(n) 
           by { lem_expn1All(); lem_expn2All(); }
    } 
  lem_funExt((n:nat) => f1(n)*f2(n), (n:nat) => (2*n)*(3*n)); 
}

lemma test_polyBigO() returns (c:nat, n0:nat)
  ensures bigO(n => 3*exp(n,2) + 100*exp(n,1) + 10, quadGrowth())
{
  var poly := n => 3*exp(n,2) + 100*exp(n,1) + 10;

  // we show that c=113 y n0=1
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

//**************************************************************************//

lemma test_log2BigOn() returns (c:nat, n0:nat)
  ensures bigO(n => log2(n+1), linGrowth())
{
  // we show that c=1 y n0=1
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