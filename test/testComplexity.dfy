include "../theory/math/ExpNat.dfy"
include "../theory/math/ExpReal.dfy"
include "../theory/math/LemBoundsNat.dfy"
include "../theory/math/LemFunction.dfy"
include "../theory/math/Log2Nat.dfy"
include "../theory/math/SumInt.dfy"
include "../theory/math/TypeR0.dfy"
include "../theory/ComplexityR0.dfy"
include "../theory/LemComplexityR0.dfy"

import EN = ExpNat
import opened ExpReal
import opened LemBoundsNat
import opened LemFunction
import opened Log2Nat
import opened SumInt
import opened TypeR0
import opened ComplexityR0
import opened LemComplexityR0

lemma test_bigOprod()
  requires liftToR0(n => 2*n) in O(linGrowth())
  requires liftToR0(n => 3*n) in O(linGrowth())
  ensures  liftToR0(n => (2*n)*(3*n)) in O(quadGrowth())
{
  var f1:nat->R0 := liftToR0(n => 2*n);
  var f2:nat->R0 := liftToR0(n => 3*n);

  lem_bigO_prod(f1, linGrowth(), f2, linGrowth());  
  assert (n => f1(n)*f2(n)) in O(n => linGrowth()(n)*linGrowth()(n));

  lem_fun_Ext(n => linGrowth()(n)*linGrowth()(n), quadGrowth())
    by { lem_fun_EtaApp(linGrowth()); 
         lem_fun_EtaApp(quadGrowth());
         forall n:nat ensures (n => linGrowth()(n)*linGrowth()(n))(n) == quadGrowth()(n) { } 
    }
  lem_fun_Ext(n => f1(n)*f2(n), liftToR0(n => (2*n)*(3*n))) 
    by { lem_fun_EtaApp(f1); lem_fun_EtaApp(f2); assert 2.0 == 2 as R0; assert 3.0 == 3 as R0; } 
}

lemma test_polyBigO() returns (c:R0, n0:nat) 
  ensures ((n:nat) => 3.0*exp(n as R0,2.0) + 100.0*exp(n as R0,1.0) + 10.0) in O(quadGrowth())
{
  var poly := ((n:nat) => 3.0*exp(n as R0,2.0) + 100.0*exp(n as R0,1.0) + 10.0);

  c, n0 := 113.0, 1;
  forall n:nat | 0 <= n0 <= n
    ensures poly(n) <= c*quadGrowth()(n)
  {
    calc {
         poly(n);
      == (3.0*exp(n as R0,2.0) + 100.0*exp(n as R0,1.0) + 10.0) as R0;
      == { lem_exp_Pow0(n as R0); }
         (3.0*exp(n as R0,2.0) + 100.0*exp(n as R0,1.0) + 10.0*exp(n as R0,0.0)) as R0;
      <= { lem_exp_MonoIncr(n as R0, 1.0, 2.0); lem_exp_MonoIncr(n as R0, 0.0, 2.0);  }
         (3.0*exp(n as R0,2.0) + 100.0*exp(n as R0,2.0) + 10.0*exp(n as R0,2.0)) as R0;
      == ((3.0 + 100.0 + 10.0)*exp(n as R0,2.0)) as R0;
      == c*exp(n as R0,2.0) as R0; 
      == { lem_exp_Pow2(n as R0); }
         c * (n*n) as R0; 
    }
  }
  assert c > 0.0 && bigOfrom(c, n0, poly, quadGrowth());
} 

// lemma test_log2BigOlin() returns (c:nat, n0:nat)
//   ensures ((n:nat) => log2(n+1)) in O(linGrowth())
// {
//   c, n0 := 1, 1;
//   forall n:nat | 0 <= n0 <= n
//     ensures log2(n+1) <= c*linGrowth()(n)
//   {
//     calc {
//          log2(n+1);
//       <= { lem_log2nPlus1LEQn(n); }
//          n;
//       == { reveal exp(); }
//          c*exp(n,1);  
//     }
//     assert log2(n+1) <= c*linGrowth()(n);
//   }
//   assert bigOfrom(c, n0, n => log2(n+1), linGrowth());
// } 