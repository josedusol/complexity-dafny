include "../theory/math/ExpNat.dfy"
include "../theory/ComplexityNat.dfy"
include "../theory/GrowthRatesNat.dfy"

import opened ExpNat
import opened ComplexityNat
import opened GrowthRatesNat

ghost function f(N:nat) : nat
{
  if N < 10 then pow(N,1) else 20 
}

method linBefore(N:nat)
  returns (ghost t:nat)
  ensures t == f(N)
  ensures tIsBigO(N, t, constGrowth())
{
  if N < 10 {
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
  } else {
    // Op. interesante ocurre 20 veces
    t := 20 ;
  }
  assert t == if N < 10 then T(N, 0) else 20;
  assert t == f(N) by { reveal pow(); lem_Tclosed(N, 0); }
  assert t <= f(N);
 
  assert bigO(f, constGrowth()) by { var c, n0 := lem_fBigOconst(); }
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

lemma lem_fBigOconst() returns (c:nat, n0:nat)
  ensures bigOfrom(c, n0, f, constGrowth())
{
  // we show that c=20 and n0=10
  c, n0 := 20, 10; 
  forall n:nat | 0 <= n0 <= n
    ensures f(n) <= c*constGrowth()(n)
  {
    calc {
        f(n);
      ==
        if n < 10 then pow(n,1) else 20;
      == { reveal pow(); }
        if n < 10 then n else 20;    
    }
    assert n >= n0 ==> f(n) <= c*constGrowth()(n);
  }
}