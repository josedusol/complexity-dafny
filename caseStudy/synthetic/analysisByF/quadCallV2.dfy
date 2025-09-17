include "../../../theory/math/Function.dfy"
include "../../../theory/math/LemFunction.dfy"
include "../../../theory/math/TypeR0.dfy"
include "../../../theory/Complexity/Asymptotics.dfy"

import opened Function
import opened LemFunction
import opened TypeR0
import opened Asymptotics

type Input {
  function size() : nat
}

ghost function f(n:nat) : nat
{
  n
}

method quadCallV2(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())*f(x.size())
  ensures tIsBigOh(x.size(), t as R0, quadGrowth())
{
  var N := x.size();
  t := 0;

  var i := 0;
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
  assert liftToR0(n => f(n)*f(n)) in O(quadGrowth()) 
    by { var c, n0 := lem_FmfBigOquad(); }
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

lemma lem_FmfBigOquad() returns (c:R0, n0:nat)
  ensures c > 0.0 && bigOhFrom(c, n0, liftToR0(n => f(n)*f(n)), quadGrowth())
{
  c, n0 := 1.0, 0;
  forall n:nat | 0 <= n0 <= n
    ensures (f(n)*f(n)) as R0 <= c*quadGrowth()(n)
  {
    calc {
         (f(n)*f(n)) as R0;
      == (n*n) as R0;
      <= c * (n*n) as R0;
      == c*quadGrowth()(n);   
    }
  }
}