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
  if n < 10 then n else 20
}

method linAfter(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
  ensures tIsBigO(x.size(), t as R0, constGrowth())
{
  var N := x.size(); reveal sum();

  if N < 10 {
    var i;
    i, t := 0, 0;
    while i != N
      invariant 0 <= i <= N
      invariant t == sum(1, i, x => 1)
      decreases N - i
    {
      // Op. interesante
      lem_sum_dropLastAll(1, i); 
      i := i+1 ;
      t := t+1 ;
    }     
  } else {
    // Op. interesante ocurre 20 veces
    t := 20 ;
  }

  assert t == if N < 10 then sum(1, N, k => 1) else 20; 
  assert t == f(N) by { lem_sum_constAll(1, N); }
  assert liftToR0(f) in O(constGrowth()) by { var c, n0 := lem_fBigOconst(); }
} 

lemma lem_fBigOconst() returns (c:R0, n0:nat)
  ensures c > 0.0 && bigOfrom(c, n0, liftToR0(f), constGrowth())
{
  c, n0 := 20.0, 10; 
  forall n:nat | 0 <= n0 <= n
    ensures f(n) as R0 <= c*constGrowth()(n)
  {
    calc {
         f(n) as R0;
      == (if n < 10 then n else 20) as R0;
      == 20 as R0;
      <= c * 1 as R0;
      == c*constGrowth()(n); 
    }
  }
}