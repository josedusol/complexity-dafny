include "../theory/math/ExpNat.dfy"
include "../theory/ComplexityNat.dfy"

import opened ExpNat
import opened ComplexityNat

ghost function f(N:nat) : nat
{
  exp(N,1)
}

method breakLinWT(N:nat, P:nat->bool)
  returns (ghost t:nat)
  ensures t == f(N)
  ensures tIsBigO(N, t, linGrowth())
{
  assume {:axiom} forall i :: 0 <= i < N ==> !P(i);  // worst case
  var i;
  i, t := 0, 0;
  while i != N
    invariant 0 <= i <= N
    invariant t == T(N,0) - T(N,i)  // = T(N, N-i)
    decreases N - i
  {
    if !P(i) { // Op. interesante
      i := i+1 ;     
    } else {
      i := N;  // break;
    }
    t := t+1 ;
  }
  assert t == T(N, 0); 
  assert t == f(N) by { reveal exp(); lem_Tclosed(N, 0); }
  assert t <= f(N);
 
  assert bigO(f, linGrowth()) by { var c, n0 := lem_fBigOlin(); }
} 

lemma lem_fBigOlin() returns (c:nat, n0:nat)
  ensures bigOfrom(c, n0, f, linGrowth())
{
  // we show that c=1 and n0=0
  c, n0 := 1, 0;
  forall n:nat | 0 <= n0 <= n
    ensures f(n) <= c*linGrowth()(n)
  {
    calc {
         f(n);
      == exp(n,1);
      == { reveal exp(); }
         n;   
    }
    assert f(n) <= c*linGrowth()(n); 
  }
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