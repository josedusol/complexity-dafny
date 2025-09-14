include "../../../theory/math/LemFunction.dfy"
include "../../../theory/math/SumInt.dfy"
include "../../../theory/math/TypeR0.dfy"
include "../../../theory/Complexity.dfy"

import opened LemFunction
import opened SumInt
import opened TypeR0
import opened Complexity

type Input {
  function size() : nat
}

ghost function f(n:nat) : nat
{
  if n < 10 then 20 else n
}

method linAfter2(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
  ensures tIsBigO(x.size(), t as R0, linGrowth())
{
  var N := x.size(); reveal sum();

  if N < 10 {
    // Op. interesante ocurre 100 veces
    t := 20 ;
  } else {
    var i;
    i, t := 0, 0;
    while i != N
      invariant 0 <= i <= N
      invariant t == sum(1, i, k => 1)
      decreases N - i
    {
      // Op. interesante
      lem_sum_DropLastAuto(1, i);
      i := i+1 ;
      t := t+1 ;
    }
  }

  assert t == if N < 10 then 20 else sum(1, N, k => 1); 
  assert t == f(N) by { lem_sum_constAll(1, N); }
  assert liftToR0(f) in O(linGrowth()) by { var c, n0 := lem_fBigOlin(); }
} 

lemma lem_fBigOlin() returns (c:R0, n0:nat)
  ensures c > 0.0 && bigOfrom(c, n0, liftToR0(f), linGrowth())
{
  c, n0 := 1.0, 10;
  forall n:nat | 0 <= n0 <= n
    ensures f(n) as R0 <= c*linGrowth()(n) 
  {
    calc {
         f(n) as R0;
      == (if n < 10 then 20 else n) as R0;
      == c * n as R0;
      == c*linGrowth()(n);    
    }
  }
}