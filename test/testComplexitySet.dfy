include "../theory/math/ExpReal.dfy"
include "../theory/math/Function.dfy"
include "../theory/math/LemBoundsNat.dfy"
include "../theory/math/LemFunction.dfy"
include "../theory/math/LogReal.dfy"
include "../theory/math/MaxMin.dfy"
include "../theory/math/SumInt.dfy"
include "../theory/math/TypeR0.dfy"
include "../theory/Complexity/Asymptotics.dfy"
include "../theory/Complexity/LemBigOh.dfy"
include "../theory/Complexity/LemBigTh.dfy"

import Exp = ExpReal
import opened Function
import opened LemBoundsNat
import opened LemFunction
import LogR = LogReal
import opened MaxMin
import opened SumInt
import opened TypeR0
import opened Asymptotics
import LemOh = LemBigOh
import LemTh = LemBigTh

lemma test_sumBigOmax(T:nat->R0, f:nat->R0, b:nat, c:R0, k:R0)
  requires forall n:nat :: T(n) == if n <= b then c else c + f(n)
  requires k >= 1.0
  requires bigOh(f, n => Exp.exp(n as R0, k))
  ensures  bigOh(T, polyGrowth(k))
{
  var d:R0, n0:nat :| d > 0.0 && bigOhFrom(d, n0, f, n => Exp.exp(n as R0, k)); // H
  assert H1: forall n:nat :: n > n0 ==> f(n) <= d*Exp.exp(n as R0, k);
  
  var c1, n1 := c+d, max(b+1, n0);
  forall n:nat | 0 <= n1 <= n
    ensures T(n) <= c1*Exp.exp(n as R0, k)
  {
    calc {
         T(n);
      == c + f(n);
      <= { reveal H1; }
         c + d*Exp.exp(n as R0, k);
      <= { assert n > 0; Exp.lem_GEQone(n as R0, k); }
         c*Exp.exp(n as R0, k) + d*Exp.exp(n as R0, k);
      == (c + d)*Exp.exp(n as R0, k);     
      == c1*Exp.exp(n as R0, k);    
    }
  }    
  assert c1 > 0.0 && bigOhFrom(c1, n1, T, polyGrowth(k));
}

lemma test_sumBigOmax2(T:nat->R0, f:nat->R0, b:nat, c:R0, k:R0)
  requires forall n:nat :: T(n) == if n <= b then c else c + f(n)
  requires k >= 1.0
  requires bigOh(f, n => Exp.exp(n as R0, k))
  ensures  bigOh(T, polyGrowth(k))
{  
  var d:R0, n0:nat :| d > 0.0 && bigOhFrom(d, n0, f, n => Exp.exp(n as R0, k)); // H
  assert H1: forall n:nat :: n > n0 ==> f(n) <= d*Exp.exp(n as R0, k);
  
  var c1, n1 := c+d, n0+1;
  forall n:nat | 0 <= n1 <= n
    ensures T(n) <= c1*Exp.exp(n as R0, k)
  {
    calc {
         T(n);
      == if n <= b then c else c + f(n);
      <= c + f(n);
      <= { reveal H1; }   
         c + d*Exp.exp(n as R0, k);
      <= { assert n > 0; Exp.lem_GEQone(n as R0, k); }
         c*Exp.exp(n as R0, k) + d*Exp.exp(n as R0, k);
      == (c + d)*Exp.exp(n as R0, k);     
      == c1*Exp.exp(n as R0, k);    
    }
  }    
  assert c1 > 0.0 && bigOhFrom(c1, n1, T, polyGrowth(k));
}

// A proof based on BigO properties
lemma test_sumBigOmax3(T:nat->R0, f:nat->R0, b:nat, c:R0 , k:R0)
  requires forall n:nat :: T(n) == if n <= b then c else c + f(n)
  requires k >= 1.0
  requires bigOh(f, n => Exp.exp(n as R0, k))
  ensures  bigOh(T, polyGrowth(k))
{
  assert forall n:nat :: n > b ==> T(n) == c + f(n);  
  var cf:nat->R0 := n => c;

  assert bigOh(T, n => cf(n) + f(n)) by {
    var c1, n0 := 1.0, b+1;    
    assert bigOhFrom(c1, n0, T, n => cf(n) + f(n));
  }

  assert bigOh(cf, constGrowth()) by {
    LemOh.lem_ConstGrowth(cf, c);
  }
  assert bigOh(cf, polyGrowth(k)) by {
    LemOh.lem_ConstInPoly(k);
    LemOh.lem_Trans(cf, constGrowth(), polyGrowth(k));
  }
  assert bigOh(f, polyGrowth(k)) by {
    var d:R0, n0f:nat :| d > 0.0 && bigOhFrom(d, n0f, f, n => Exp.exp(n as R0, k)); // H
    assert bigOhFrom(d, n0f, n => f(n), polyGrowth(k));
  }    

  assert bigOh(n => cf(n) + f(n), n => polyGrowth(k)(n) + polyGrowth(k)(n)) by {
    LemOh.lem_Sum(cf, polyGrowth(k), f, polyGrowth(k));  
  }

  assert bigOh(n => polyGrowth(k)(n) + polyGrowth(k)(n), polyGrowth(k)) by {
    LemOh.lem_Refl(polyGrowth(k));  
    LemOh.lem_SumSimpl(polyGrowth(k), polyGrowth(k));  
    LemTh.lem_DefEqDef2(n => polyGrowth(k)(n) + polyGrowth(k)(n), polyGrowth(k));
  }

  LemOh.lem_Trans(T, n => cf(n) + f(n), n => polyGrowth(k)(n) + polyGrowth(k)(n));
  LemOh.lem_Trans(T, n => polyGrowth(k)(n) + polyGrowth(k)(n), polyGrowth(k));
} 

// A variation of previous proof with a little shortcut
lemma test_sumBigOmax4(T:nat->R0, f:nat->R0, b:nat, c:R0 , k:R0)
  requires forall n:nat :: T(n) == if n <= b then c else c + f(n)
  requires k >= 1.0
  requires bigOh(f, n => Exp.exp(n as R0, k))
  ensures  bigOh(T, polyGrowth(k))
{
  assert forall n:nat :: n > b ==> T(n) == c + f(n);  
  var cf:nat->R0 := n => c;

  assert bigOh(T, n => cf(n) + f(n)) by {
    var c1, n0 := 1.0, b+1;    
    assert bigOhFrom(c1, n0, T, n => cf(n) + f(n));
  }

  assert bigOh(cf, constGrowth()) by {
    LemOh.lem_ConstGrowth(cf, c);
  }
  assert bigOh(f, polyGrowth(k)) by {
    var d:R0, n0f:nat :| d > 0.0 && bigOhFrom(d, n0f, f, n => Exp.exp(n as R0, k)); // H
    assert bigOhFrom(d, n0f, n => f(n), polyGrowth(k));
  }    

  assert bigOh(n => cf(n) + f(n), n => constGrowth()(n) + polyGrowth(k)(n)) by {
    LemOh.lem_Sum(cf, constGrowth(), f, polyGrowth(k));  
  }

  assert bigOh(n => constGrowth()(n) + polyGrowth(k)(n), polyGrowth(k)) by {
    LemOh.lem_ConstInPoly(k);
    LemOh.lem_SumSimpl(constGrowth(), polyGrowth(k));
    LemTh.lem_DefEqDef2(n => constGrowth()(n) + polyGrowth(k)(n), polyGrowth(k));
  }

  LemOh.lem_Trans(T, n => cf(n) + f(n), n => constGrowth()(n) + polyGrowth(k)(n));
  LemOh.lem_Trans(T, n => constGrowth()(n) + polyGrowth(k)(n), polyGrowth(k));
} 

// A more idiomatic version of previous proof trying to express it as a deduction chain
lemma test_sumBigOmax5(T:nat->R0, f:nat->R0, b:nat, c:R0 , k:R0)
  requires forall n:nat :: T(n) == if n <= b then c else c + f(n)
  requires k >= 1.0
  requires bigOh(f, n => Exp.exp(n as R0, k))
  ensures  bigOh(T, polyGrowth(k))
{
  assert forall n:nat :: n > b ==> T(n) == c + f(n);  
  var cf:nat->R0 := n => c;

  assert bigOh(T, n => cf(n) + f(n)) by {
    var c1, n0 := 1.0, b+1;    
    assert bigOhFrom(c1, n0, T, n => cf(n) + f(n));
  }
  assert bigOh(cf, constGrowth()) by {
    LemOh.lem_ConstGrowth(cf, c);
  }
  assert bigOh(f, polyGrowth(k)) by {
    var d:R0, n0f:nat :| d > 0.0 && bigOhFrom(d, n0f, f, n => Exp.exp(n as R0, k)); // H
    assert bigOhFrom(d, n0f, n => f(n), polyGrowth(k));
  }    

  calc {
        bigOh(T, n => cf(n) + f(n));
    ==> { LemOh.lem_Sum(cf, constGrowth(), f, polyGrowth(k)); 
          LemOh.lem_Trans(T, n => cf(n) + f(n), n => constGrowth()(n) + polyGrowth(k)(n)); }
        bigOh(T, n => constGrowth()(n) + polyGrowth(k)(n));
    ==> { LemOh.lem_ConstInPoly(k); 
          LemOh.lem_SumSimpl(constGrowth(), polyGrowth(k)); 
          LemTh.lem_DefEqDef2(n => constGrowth()(n) + polyGrowth(k)(n), polyGrowth(k));
          LemOh.lem_Trans(T, n => constGrowth()(n) + polyGrowth(k)(n), polyGrowth(k));}
        bigOh(T, polyGrowth(k));    
  }
}

// A set theoretic version as a subset deduction chain
//   T ∈ O(c+f)
//     ⊆ O(c+f)
//     ⊆ O(1+n^k)
//     = O(n^k)
lemma test_sumBigOmax6(T:nat->R0, f:nat->R0, b:nat, c:R0 , k:R0)
  requires forall n:nat :: T(n) == if n <= b then c else c + f(n)
  requires k >= 1.0
  requires f in O(n => Exp.exp(n as R0, k))
  ensures  T in O(polyGrowth(k))
{
  assert forall n:nat :: n > b ==> T(n) == c + f(n);  
  var cf:nat->R0 := n => c;

  assert cf in O(constGrowth()) by {
    LemOh.lem_ConstGrowth(cf, c);
  }
  assert f in O(polyGrowth(k)) by {
    var d:R0, n0f:nat :| d > 0.0 && bigOhFrom(d, n0f, f, n => Exp.exp(n as R0, k)); // H
    assert bigOhFrom(d, n0f, n => f(n), polyGrowth(k));
  }    

  assert T in O(n => cf(n) + f(n)) by {
    var c1, n0 := 1.0, b+1;    
    assert bigOhFrom(c1, n0, T, n => cf(n) + f(n));
  }
  calc {
        O(n => cf(n) + f(n));
     <= { LemOh.lem_SumSet(cf, constGrowth(), f, polyGrowth(k)); }
        O(n => constGrowth()(n) + polyGrowth(k)(n));
     == { LemOh.lem_ConstInPoly(k); 
          LemOh.lem_SumSimplSet(constGrowth(), polyGrowth(k)); }
        O(polyGrowth(k));   
  }
}