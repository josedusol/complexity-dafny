include "../theory/math/ExpNat.dfy"
include "../theory/math/LemFunction.dfy"
include "../theory/ComplexityNat.dfy"
include "../theory/LemComplexityNat.dfy"

import opened ExpNat
import opened LemFunction
import opened ComplexityNat
import opened LemComplexityNat

ghost function f(N:nat) : nat
{
  N
}

method quadCallV2(N:nat)
  returns (ghost t:nat)
  ensures t == f(N)*f(N)
  ensures tIsBigO(N, t, quadGrowth())
{
  var i;
  i, t := 0, 0;
  while i != N
    invariant 0 <= i <= N
    invariant t == f(i)*f(N)  // = T1(N, N-i)
    decreases N - i
  {
    var t' := quadCallSub(N);
    i := i+1;
    t := t + t'; 
  }
  assert t == f(N)*f(N); 
  assert t <= f(N)*f(N); 
  assert (n => f(n)*f(n)) in O(quadGrowth()) by {
    lem_bigO_refl(n => f(n)*f(n));
    assert forall n:nat :: f(n)*f(n) == quadGrowth()(n) 
      by { lem_expn2All(); }
    lem_funExt(n => f(n)*f(n), quadGrowth());
  }
} 

method quadCallSub(N:nat)
  returns (ghost t:nat)
  ensures t == f(N)
{
  var i;
  i, t := 0, 0;
  while i != N
    invariant 0 <= i <= N
    invariant t == f(i)  // = T1(N, N-i)
    decreases N - i
  {
    // Op. interesante
    i := i+1;
    t := t+1;
  }
  assert t == f(N); 
} 