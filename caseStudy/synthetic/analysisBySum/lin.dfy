include "../../../theory/math/Function.dfy"
include "../../../theory/math/LemFunction.dfy"
include "../../../theory/math/intervalOp/SumInt.dfy"
include "../../../theory/math/TypeR0.dfy"
include "../../../theory/Complexity/Asymptotics.dfy"

import opened Function
import opened LemFunction
import opened SumInt
import opened TypeR0
import opened Asymptotics

type Input {
  function size() : nat
}

ghost function f(n:nat) : nat
{
  n
}

method lin(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
  ensures tIsBigOh(x.size(), t as R0, linGrowth())
{
  var N := x.size();
  t := 0; reveal ISN.bigOp(); 

  var i;
  i := 0;
  while i != N
    invariant 0 <= i <= N
    invariant t == sum(1, i, k => 1)
    decreases N - i
  {
    // Op. interesante
    ISN.lem_SplitLastAuto(1, i+1);
    i := i+1 ;
    t := t+1 ;
  }

  assert t == sum(1, N, k => 1); 
  assert t == f(N) by { lem_ConstAuto(1, N); }
  assert liftToR0(f) in O(linGrowth()) by { var c, n0 := lem_fBigOlin(); }
} 

method linFor(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
  ensures tIsBigOh(x.size(), t as R0, linGrowth())
{
  var N := x.size();
  t := 0; reveal ISN.bigOp();
  
  for i := 0 to N
    invariant t == sum(1, i, k => 1)
  {
    // Op. interesante
    ISN.lem_SplitLastAuto(1, i+1);
    t := t+1 ;
  }

  assert t == sum(1, N, k => 1); 
  assert t == f(N) by { lem_ConstAuto(1, N); }
  assert t <= f(N);
  assert liftToR0(f) in O(linGrowth()) by { var c, n0 := lem_fBigOlin(); }
}

lemma lem_fBigOlin() returns (c:R0, n0:nat)
  ensures c > 0.0 && bigOhFrom(c, n0, liftToR0(f), linGrowth())
{
  c, n0 := 1.0, 0;
  forall n:nat | 0 <= n0 <= n
    ensures f(n) as R0 <= c*linGrowth()(n)
  {
    calc {
         f(n) as R0;
      == n as R0;
      <= c * n as R0;
      == c*linGrowth()(n); 
    }
  }
}