include "../theory/math/ExpReal.dfy"
include "../theory/math/LemBoundsNat.dfy"
include "../theory/math/LemFunction.dfy"
include "../theory/math/Log2Nat.dfy"
include "../theory/math/MaxMin.dfy"
include "../theory/math/SumInt.dfy"
include "../theory/math/TypeR0.dfy"
include "../theory/ComplexityR0.dfy"
include "../theory/LemComplexityR0.dfy"

import opened ExpReal
import opened LemBoundsNat
import opened LemFunction
import opened Log2Nat
import opened MaxMin
import opened SumInt
import opened TypeR0
import opened ComplexityR0
import opened LemComplexityR0

lemma test_sumBigOmax(T:nat->R0, f:nat->R0, b:nat, c:R0, k:R0)
  requires forall n:nat :: T(n) == if n <= b then c else c + f(n)
  requires k >= 1.0
  requires bigO(f, n => exp(n as R0, k))
  ensures  bigO(T, polyGrowth(k))
{
  var d:R0, n0:nat :| bigOfrom(d, n0, f, n => exp(n as R0, k)); // H
  assert forall n:nat :: n > n0 ==> f(n) <= d*exp(n as R0, k);
  
  var c1, n1 := c+d, max(b+1, n0);
  forall n:nat | 0 <= n1 <= n
    ensures T(n) <= c1*exp(n as R0, k)
  {
    calc {
         T(n);
      == c + f(n);
      <= c + d*exp(n as R0, k);
      <= { assert n > 0; lem_expGEQone(n as R0, k); }
         c*exp(n as R0, k) + d*exp(n as R0, k);
      == (c + d)*exp(n as R0, k);     
      == c1*exp(n as R0, k);    
    }
  }    
  assert bigOfrom(c1, n1, T, polyGrowth(k));
}

lemma test_sumBigOmax2(T:nat->R0, f:nat->R0, b:nat, c:R0, k:R0)
  requires forall n:nat :: T(n) == if n <= b then c else c + f(n)
  requires k >= 1.0
  requires bigO(f, n => exp(n as R0, k))
  ensures  bigO(T, polyGrowth(k))
{  
  var d:R0, n0:nat :| bigOfrom(d, n0, f, n => exp(n as R0, k)); // H
  assert forall n:nat :: n > n0 ==> f(n) <= d*exp(n as R0, k);
  
  var c1, n1 := c+d, n0+1;
  forall n:nat | 0 <= n1 <= n
    ensures T(n) <= c1*exp(n as R0, k)
  {
    calc {
         T(n);
      == if n <= b then c else c + f(n);
      <= c + d*exp(n as R0, k);
      <= { assert n > 0; lem_expGEQone(n as R0, k); }
         c*exp(n as R0, k) + d*exp(n as R0, k);
      == (c + d)*exp(n as R0, k);     
      == c1*exp(n as R0, k);    
    }
  }    
  assert bigOfrom(c1, n1, T, polyGrowth(k));
}

// A proof based on BigO properties
lemma test_sumBigOmax3(T:nat->R0, f:nat->R0, b:nat, c:R0 , k:R0)
  requires forall n:nat :: T(n) == if n <= b then c else c + f(n)
  requires k >= 1.0
  requires bigO(f, n => exp(n as R0, k))
  ensures  bigO(T, polyGrowth(k))
{
  assert forall n:nat :: n > b ==> T(n) == c + f(n);  
  var cf:nat->R0 := n => c;

  assert bigO(T, n => cf(n) + f(n)) by {
    var c1, n0 := 1.0, b+1;    
    assert bigOfrom(c1, n0, T, n => cf(n) + f(n));
  }

  assert bigO(cf, constGrowth()) by {
    lem_bigO_constGrowth(cf, c);
  }
  assert bigO(cf, polyGrowth(k)) by {
    lem_bigO_constBigOpoly(k);
    lem_bigO_trans(cf, constGrowth(), polyGrowth(k));
  }
  assert bigO(f, polyGrowth(k)) by {
    var d:R0, n0f:nat :| bigOfrom(d, n0f, f, n => exp(n as R0, k)); // H
    assert bigOfrom(d, n0f, n => f(n), polyGrowth(k));
  }    

  assert bigO(n => cf(n) + f(n), n => polyGrowth(k)(n) + polyGrowth(k)(n)) by {
    lem_bigO_sum(cf, polyGrowth(k), f, polyGrowth(k));  
  }

  assert bigO(n => polyGrowth(k)(n) + polyGrowth(k)(n), polyGrowth(k)) by {
    lem_bigO_refl(polyGrowth(k));  
    lem_bigO_sumSimp(polyGrowth(k), polyGrowth(k));  
  }

  lem_bigO_trans(T, n => cf(n) + f(n), n => polyGrowth(k)(n) + polyGrowth(k)(n));
  lem_bigO_trans(T, n => polyGrowth(k)(n) + polyGrowth(k)(n), polyGrowth(k));
} 

// A variation of previous proof with a little shortcut
lemma test_sumBigOmax4(T:nat->R0, f:nat->R0, b:nat, c:R0 , k:R0)
  requires forall n:nat :: T(n) == if n <= b then c else c + f(n)
  requires k >= 1.0
  requires bigO(f, n => exp(n as R0, k))
  ensures  bigO(T, polyGrowth(k))
{
  assert forall n:nat :: n > b ==> T(n) == c + f(n);  
  var cf:nat->R0 := n => c;

  assert bigO(T, n => cf(n) + f(n)) by {
    var c1, n0 := 1.0, b+1;    
    assert bigOfrom(c1, n0, T, n => cf(n) + f(n));
  }

  assert bigO(cf, constGrowth()) by {
    lem_bigO_constGrowth(cf, c);
  }
  assert bigO(f, polyGrowth(k)) by {
    var d:R0, n0f:nat :| bigOfrom(d, n0f, f, n => exp(n as R0, k)); // H
    assert bigOfrom(d, n0f, n => f(n), polyGrowth(k));
  }    

  assert bigO(n => cf(n) + f(n), n => constGrowth()(n) + polyGrowth(k)(n)) by {
    lem_bigO_sum(cf, constGrowth(), f, polyGrowth(k));  
  }

  assert bigO(n => constGrowth()(n) + polyGrowth(k)(n), polyGrowth(k)) by {
    lem_bigO_constBigOpoly(k);
    lem_bigO_sumSimp(constGrowth(), polyGrowth(k));
  }

  lem_bigO_trans(T, n => cf(n) + f(n), n => constGrowth()(n) + polyGrowth(k)(n));
  lem_bigO_trans(T, n => constGrowth()(n) + polyGrowth(k)(n), polyGrowth(k));
} 

// A more idiomatic version of previous proof trying to express it as a deduction chain
lemma test_sumBigOmax5(T:nat->R0, f:nat->R0, b:nat, c:R0 , k:R0)
  requires forall n:nat :: T(n) == if n <= b then c else c + f(n)
  requires k >= 1.0
  requires bigO(f, n => exp(n as R0, k))
  ensures  bigO(T, polyGrowth(k))
{
  assert forall n:nat :: n > b ==> T(n) == c + f(n);  
  var cf:nat->R0 := n => c;

  assert bigO(T, n => cf(n) + f(n)) by {
    var c1, n0 := 1.0, b+1;    
    assert bigOfrom(c1, n0, T, n => cf(n) + f(n));
  }
  assert bigO(cf, constGrowth()) by {
    lem_bigO_constGrowth(cf, c);
  }
  assert bigO(f, polyGrowth(k)) by {
    var d:R0, n0f:nat :| bigOfrom(d, n0f, f, n => exp(n as R0, k)); // H
    assert bigOfrom(d, n0f, n => f(n), polyGrowth(k));
  }    

  calc {
        bigO(T, n => cf(n) + f(n));
    ==> { lem_bigO_sum(cf, constGrowth(), f, polyGrowth(k)); 
          lem_bigO_trans(T, n => cf(n) + f(n), n => constGrowth()(n) + polyGrowth(k)(n)); }
        bigO(T, n => constGrowth()(n) + polyGrowth(k)(n));
    ==> { lem_bigO_constBigOpoly(k); 
          lem_bigO_sumSimp(constGrowth(), polyGrowth(k)); 
          lem_bigO_trans(T, n => constGrowth()(n) + polyGrowth(k)(n), polyGrowth(k));}
        bigO(T, polyGrowth(k));    
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
  requires f in O(n => exp(n as R0, k))
  ensures  T in O(polyGrowth(k))
{
  assert forall n:nat :: n > b ==> T(n) == c + f(n);  
  var cf:nat->R0 := n => c;

  assert cf in O(constGrowth()) by {
    lem_bigO_constGrowth(cf, c);
  }
  assert f in O(polyGrowth(k)) by {
    var d:R0, n0f:nat :| bigOfrom(d, n0f, f, n => exp(n as R0, k)); // H
    assert bigOfrom(d, n0f, n => f(n), polyGrowth(k));
  }    

  assert T in O(n => cf(n) + f(n)) by {
    var c1, n0 := 1.0, b+1;    
    assert bigOfrom(c1, n0, T, n => cf(n) + f(n));
  }
  calc {
        O(n => cf(n) + f(n));
     <= { lem_bigOset_sum(cf, constGrowth(), f, polyGrowth(k)); }
        O(n => constGrowth()(n) + polyGrowth(k)(n));
     == { lem_bigO_constBigOpoly(k); 
          lem_bigOset_sumSimp(constGrowth(), polyGrowth(k)); }
        O(polyGrowth(k));   
  }
}