include "../theory/math/ExpNat.dfy"
include "../theory/math/SumInt.dfy"
include "../theory/ComplexityNat.dfy"

import opened ExpNat
import opened SumInt
import opened ComplexityNat

type Input {
  function size() : nat
}

ghost function f(N:nat) : nat
{
  if N < 10 then 20 else exp(N,1)
}

method linAfter2(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
  ensures tIsBigO(x.size(), t, linGrowth())
{
  var N := x.size();
  reveal sum();
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
      lem_sum_dropLastAll(1, i);
      i := i+1 ;
      t := t+1 ;
    }
  }
  assert t == if N < 10 then 20 else sum(1, N, k => 1); 
  assert t == f(N) by { reveal exp(); lem_sum_constAll(1, N); }
  assert t <= f(N);
  assert f in O(linGrowth()) by { var c, n0 := lem_fBigOlin(); }
} 

lemma lem_fBigOlin() returns (c:nat, n0:nat)
  ensures bigOfrom(c, n0, f, linGrowth())
{
  // we show that c=1 and n0=10
  c, n0 := 1, 10;
  forall n:nat | 0 <= n0 <= n
    ensures f(n) <= c*linGrowth()(n) 
  {
    calc {
         f(n);
      == if n < 10 then 20 else exp(n,1);
      == { reveal exp(); }
         if n < 10 then 20 else n;   
    }
    assert f(n) <= c*linGrowth()(n);
  }
}