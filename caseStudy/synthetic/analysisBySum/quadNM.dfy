include "../../../theory/math/ExpNat.dfy"
include "../../../theory/math/SumInt.dfy"
include "../../../theory/ComplexityNat.dfy"

import opened ExpNat
import opened SumInt
import opened ComplexityNat

type Input {
  function size() : nat
}

ghost function f(N:nat, M:nat) : nat
{
  N*M
}

method quadNM(x:Input, y:Input) returns (ghost t:nat, ghost t':nat)
  ensures t == f(x.size(), y.size())
  ensures x.size() == y.size() ==> tIsBigO(x.size(), t, quadGrowth())
{
  var N, M := x.size(), y.size();
  var i, j; reveal sum();
  i, j, t, t' := 0, 0, 0, 0;
  while i != N
      invariant 0 <= i <= N
      invariant t == sum(1, i, k => sum(1, M, k' => 1))
      decreases N - i
  {
    j := 0; t' := 0;
    while j != M
      invariant 0 <= j <= M
      invariant t' == sum(1, j, k' => 1)
      decreases M - j
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
  assert t == sum(1, N, k => sum(1, M, k' => 1)); 
  assert t == f(N,M) by { lem_sum_constAll(1, M); lem_sum_constAll(1, N); }
  assert t <= f(N,M);
 
  assert N == M ==> t == (n => f(n,n))(N);
  assert (n => f(n,n)) in O(quadGrowth()) by { var c, n0 := lem_fBigOquad(); }
} 

lemma lem_fBigOquad() returns (c:nat, n0:nat)
  ensures bigOfrom(c, n0, n => f(n,n), quadGrowth())
{
  c, n0 := 1, 0;
  forall n:nat | 0 <= n0 <= n
    ensures f(n,n) <= c*quadGrowth()(n)
  { 
    calc {
         f(n,n);
      == n*n;  
      == { reveal exp(); }
         exp(n,2); 
    }
    assert f(n,n) <= c*quadGrowth()(n); 
  }
}