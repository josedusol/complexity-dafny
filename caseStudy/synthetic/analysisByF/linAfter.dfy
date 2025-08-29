include "../../../theory/math/ExpNat.dfy"
include "../../../theory/ComplexityNat.dfy"

import opened ExpNat
import opened ComplexityNat

type Input {
  function size() : nat
}

ghost function f(N:nat) : nat
{
  if N < 10 then 20 else exp(N,1)
}

method linAfter(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
  ensures tIsBigO(x.size(), t, linGrowth())
{
  var N := x.size();
  if N < 10 {
    // Op. interesante ocurre 20 veces
    t := 20 ;
  } else {
    var i;
    i, t := 0, 0;
    while i != N
      invariant 0 <= i <= N
      invariant t == T(N,0) - T(N,i)  // = T(N, N-i)
      decreases N - i
    {
      // Op. interesante
      i := i+1 ;
      t := t+1 ;
    }
  }
  assert t == if N < 10 then 20 else T(N, 0); 
  assert t == f(N) by { reveal exp(); lem_Tclosed(N, 0); }
  assert t <= f(N);
  assert f in O(linGrowth()) by { var c, n0 := lem_fBigOlin(); }
} 

ghost function T(N:nat, i:nat): nat
  requires 0 <= i <= N
  decreases N - i
{
  if i != N
  then T(N, i+1) + 1 
  else 0
}

lemma lem_Tclosed(N:nat, i:nat)
  requires 0 <= i <= N
  decreases N - i
  ensures T(N, i) == N - i
{  
}

lemma lem_fBigOlin() returns (c:nat, n0:nat)
  ensures c > 0 && bigOfrom(c, n0, f, linGrowth())
{
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