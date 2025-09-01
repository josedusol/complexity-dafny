include "../../../theory/math/ExpNat.dfy"
include "../../../theory/math/SumInt.dfy"
include "../../../theory/ComplexityNat.dfy"

import opened ExpNat
import opened SumInt
import opened ComplexityNat

type Input {
  function size() : nat
}

ghost function f(N:nat) : nat
{
  exp(N,2)
}

method quad(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
  ensures tIsBigO(x.size(), t, quadGrowth())
{
  var N := x.size();
  t := 0; reveal sum();

  var i, j;
  i, j := 0, 0 ;
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
  assert t == f(N) by { reveal exp(); lem_sum_constAll(1, N); }
  assert t <= f(N);
  assert f in O(quadGrowth()) by { var c, n0 := lem_fBigOquad(); }
} 

method quadFor(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
  ensures tIsBigO(x.size(), t, quadGrowth())
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
  assert t == f(N) by { reveal exp(); lem_sum_constAll(1, N); }
  assert t <= f(N);
  assert f in O(quadGrowth()) by { var c, n0 := lem_fBigOquad(); }
}

lemma lem_fBigOquad() returns (c:nat, n0:nat)
  ensures c > 0 && bigOfrom(c, n0, f, quadGrowth())
{
  c, n0 := 1, 0;
  forall n:nat | 0 <= n0 <= n
    ensures f(n) <= c*quadGrowth()(n)
  {
    calc {
         f(n); 
      == exp(n,2);
      == { reveal exp(); }
         n*n;   
    }
    assert f(n) <= c*quadGrowth()(n); 
  }
}