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
  n*n
}

method quad(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
  ensures tIsBigOh(x.size(), t as R0, quadGrowth())
{
  var N := x.size();
  t := 0; reveal ISN.bigOp(); 

  var i, j := 0, 0;
  while i != N
      invariant 0 <= i <= N
      invariant t == sum(1, i, k => sum(1, N, k' => 1))
      decreases N - i
  {
    j := 0; ghost var t' := 0;
    while j != N
      invariant 0 <= j <= N
      invariant t' == sum(1, j, k' => 1)
      decreases N - j
    {
      // Op. interesante
      ISN.lem_SplitLastAuto(1, j+1);
      j := j+1 ;
      t' := t'+1 ;
    }
    ISN.lem_SplitLastAuto(1, i+1);
    i := i+1 ;
    t := t+t' ;
  }

  assert t == sum(1, N, k => sum(1, N, k' => 1)); 
  assert t == f(N) by { lem_ConstAuto(1, N); }
  assert liftToR0(f) in O(quadGrowth()) by { var c, n0 := lem_fBigOquad(); }
} 

method quadFor(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
  ensures tIsBigOh(x.size(), t as R0, quadGrowth())
{
  var N := x.size();
  t := 0; reveal ISN.bigOp();

  for i := 0 to N
    invariant t == sum(1, i, k => sum(1, N, k' => 1))
  {
    ghost var t' := 0;
    for j := 0 to N
      invariant t' == sum(1, j, k' => 1)
    {
      // Op. interesante
      ISN.lem_SplitLastAuto(1, j+1);
      t' := t'+1;
    }
    ISN.lem_SplitLastAuto(1, i+1);
    t := t+t';
  }
  
  assert t == sum(1, N, k => sum(1, N, k' => 1)); 
  assert t == f(N) by { lem_ConstAuto(1, N); }
  assert liftToR0(f) in O(quadGrowth()) by { var c, n0 := lem_fBigOquad(); }
}

lemma lem_fBigOquad() returns (c:R0, n0:nat)
  ensures c > 0.0 && bigOhFrom(c, n0, liftToR0(f), quadGrowth())
{
  c, n0 := 1.0, 0;
  forall n:nat | 0 <= n0 <= n
    ensures f(n) as R0 <= c*quadGrowth()(n)
  {
    calc {
         f(n) as R0;
      == (n*n) as R0;
      <= c * (n*n) as R0;
      == c*quadGrowth()(n);   
    }
  }
}