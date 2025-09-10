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
  3*n
}

method lin(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
  ensures tIsBigO(x.size(), t as R0, linGrowth())
{
  var N := x.size(); reveal sum(); 
  t := 0;
  
  var i, j := 0, 0;
  while i != 3
      invariant 0 <= i <= 3
      invariant t == sum(1, i, k => sum(1, N, k' => 1))
      decreases 3 - i
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
  assert t == sum(1, 3, k => sum(1, N, k' => 1)); 
  assert t == f(N) by { lem_sum_constAll(1, N); }
  assert liftToR0(f) in O(linGrowth()) by { var c, n0 := lem_fBigOlin(); }
} 

lemma lem_fBigOlin() returns (c:R0, n0:nat)
  ensures c > 0.0 && bigOfrom(c, n0, liftToR0(f), linGrowth())
{
  c, n0 := 3.0, 0;
  forall n:nat | 0 <= n0 <= n
    ensures f(n) as R0 <= c*linGrowth()(n)
  {
    calc {
         f(n) as R0;
      == (3*n) as R0;
      == c*linGrowth()(n);  
    }
  }
}