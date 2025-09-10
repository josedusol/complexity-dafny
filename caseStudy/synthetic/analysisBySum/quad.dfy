include "../../../theory/math/LemFunction.dfy"
include "../../../theory/math/SumInt.dfy"
include "../../../theory/math/TypeR0.dfy"
include "../../../theory/ComplexityR0.dfy"

import opened LemFunction
import opened SumInt
import opened TypeR0
import opened ComplexityR0

type Input {
  function size() : nat
}

ghost function f(n:nat) : nat
{
  n*n
}

method quad(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
  ensures tIsBigO(x.size(), t as R0, quadGrowth())
{
  var N := x.size();
  t := 0; reveal sum();

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
      lem_sum_dropLastAll(1, j); 
      j := j+1 ;
      t' := t'+1 ;
    }
    lem_sum_dropLastAll(1, i);
    i := i+1 ;
    t := t+t' ;
  }

  assert t == sum(1, N, k => sum(1, N, k' => 1)); 
  assert t == f(N) by { lem_sum_constAll(1, N); }
  assert liftToR0(f) in O(quadGrowth()) by { var c, n0 := lem_fBigOquad(); }
} 

method quadFor(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
  ensures tIsBigO(x.size(), t as R0, quadGrowth())
{
  var N := x.size();
  t := 0; reveal sum();

  for i := 0 to N
    invariant t == sum(1, i, k => sum(1, N, k' => 1))
  {
    ghost var t' := 0;
    for j := 0 to N
      invariant t' == sum(1, j, k' => 1)
    {
      // Op. interesante
      lem_sum_dropLastAll(1, j); 
      t' := t'+1;
    }
    lem_sum_dropLastAll(1, i);
    t := t+t';
  }
  
  assert t == sum(1, N, k => sum(1, N, k' => 1)); 
  assert t == f(N) by { lem_sum_constAll(1, N); }
  assert liftToR0(f) in O(quadGrowth()) by { var c, n0 := lem_fBigOquad(); }
}

lemma lem_fBigOquad() returns (c:R0, n0:nat)
  ensures c > 0.0 && bigOfrom(c, n0, liftToR0(f), quadGrowth())
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