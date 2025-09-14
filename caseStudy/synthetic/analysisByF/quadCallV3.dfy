include "../../../theory/math/LemFunction.dfy"
include "../../../theory/math/TypeR0.dfy"
include "../../../theory/Complexity.dfy"
include "../../../theory/LemComplexityBigOh.dfy"

import opened LemFunction
import opened TypeR0
import opened Complexity
import opened LemComplexityBigOh

type Input {
  function size() : nat
}

ghost function f(n:nat) : nat
{
  n
}

method quadCallV2(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())*f(x.size())
  ensures tIsBigO(x.size(), t as R0, quadGrowth())
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
  assert liftToR0(n => f(n)*f(n)) in O(quadGrowth()) by {
    lem_bigO_refl(liftToR0(n => f(n)*f(n)));
    assert forall n:nat :: (f(n)*f(n)) as R0 == quadGrowth()(n);
    lem_fun_Ext(liftToR0(n => f(n)*f(n)), quadGrowth());
  }
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