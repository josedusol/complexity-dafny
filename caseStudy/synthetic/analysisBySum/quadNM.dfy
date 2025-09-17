include "../../../theory/math/Function.dfy"
include "../../../theory/math/LemFunction.dfy"
include "../../../theory/math/SumInt.dfy"
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

ghost function f(n:nat, m:nat) : nat
{
  n*m
}

method quadNM(x:Input, y:Input) returns (ghost t:nat)
  ensures t == f(x.size(), y.size())
  ensures x.size() == y.size() ==> tIsBigOh(x.size(), t as R0, quadGrowth())
{
  var N, M := x.size(), y.size(); 
  t := 0; reveal sum();

  var i, j := 0, 0;
  while i != N
      invariant 0 <= i <= N
      invariant t == sum(1, i, k => sum(1, M, k' => 1))
      decreases N - i
  {
    j := 0; ghost var t' := 0;
    while j != M
      invariant 0 <= j <= M
      invariant t' == sum(1, j, k' => 1)
      decreases M - j
    {
      // Op. interesante
      lem_DropLastAuto(1, j); 
      j := j+1 ;
      t' := t'+1 ;
    }
    lem_DropLastAuto(1, i);
    i := i+1 ;
    t := t+t' ;
  }

  assert t == sum(1, N, k => sum(1, M, k' => 1)); 
  assert t == f(N,M) by { lem_ConstAuto(1, M); lem_ConstAuto(1, N); }
  assert N == M ==> t == (n => f(n,n))(N);
  assert liftToR0(n => f(n,n)) in O(quadGrowth()) by { var c, n0 := lem_fBigOquad(); }
} 

lemma lem_fBigOquad() returns (c:R0, n0:nat)
  ensures c > 0.0 && bigOhFrom(c, n0, liftToR0(n => f(n,n)), quadGrowth())
{
  c, n0 := 1.0, 0;
  forall n:nat | 0 <= n0 <= n
    ensures f(n,n) as R0 <= c*quadGrowth()(n)
  {
    calc {
         f(n,n) as R0;
      == (n*n) as R0;  
      <= c * (n*n) as R0;
      == c*quadGrowth()(n); 
    }
  }
}