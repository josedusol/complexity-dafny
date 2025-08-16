include "../theory/math/ExpNat.dfy"
include "../theory/ComplexityNat.dfy"

import opened ExpNat
import opened ComplexityNat

type Input {
  function size() : nat
}

ghost function f(N:nat) : nat
{
  N
}

method quadCallV2(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())*f(x.size())
  ensures tIsBigO(x.size(), t, quadGrowth())
{
  var N := x.size();
  var i;
  i, t := 0, 0;
  while i != N
    invariant 0 <= i <= N
    invariant t == f(i)*f(N)  // = T1(N, N-i)
    decreases N - i
  {
    var t' := quadCallSub(x);
    i := i+1;
    t := t + t'; 
  }
  assert t == f(N)*f(N); 
  assert t <= f(N)*f(N); 
  assert (n => f(n)*f(n)) in O(quadGrowth()) 
    by { var c, n0 := lem_fmfBigOquad(); }
} 

method quadCallSub(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
{
  var N := x.size();
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

lemma lem_fmfBigOquad() returns (c:nat, n0:nat)
  ensures bigOfrom(c, n0, n => f(n)*f(n), quadGrowth())
{
  // we show that c=1 and n0=0
  c, n0 := 1, 0;
  forall n:nat | 0 <= n0 <= n
    ensures f(n)*f(n) <= c*quadGrowth()(n)
  {
    calc {
         f(n)*f(n);
      == n*n;
      == { reveal exp(); }
         exp(n,2);   
    }
    assert f(n)*f(n) <= c*quadGrowth()(n); 
  }
}