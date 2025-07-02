include "../theory/math/ExpReal.dfy"
include "../theory/math/LemFunction.dfy"
include "../theory/math/SumReal.dfy"
include "../theory/math/TypeR0.dfy"
include "../theory/ComplexityNat.dfy"

import opened ExpReal
import opened LemFunction
import opened SumReal
import opened TypeR0
import opened ComplexityNat

ghost predicate inv<A>(s:seq<A>, x:A, i:nat, N:int)
{
     0 <= i <= N && N <= |s|
  && (0 <= N < |s| ==> s[i] == x)      
  && (N == |s|     ==> (forall j :: 0 <= j < i ==> s[j] != x))
}

ghost predicate post<A>(s:seq<A>, x:A, i:nat)
{
     (0 <= i < |s| ==> s[i] == x)
  && (i == |s|     ==> (forall j :: 0 <= j < |s| ==> s[j] != x))
}

ghost function f(N:nat) : nat
{
  1
}

ghost method linearSearch<A>(s:seq<A>, x:A) returns (i:nat, t:nat)
  ensures post(s, x, i)
  ensures t <= f(|s|) 
  ensures tIsBigO(|s|, t, constGrowth())
{
  assume {:axiom} |s| > 0 ==> s[0] == x;  // best case
  var N;
  i, N, t := 0, |s|, 0;
  while i != N
    invariant inv(s, x, i, N)
    invariant (i == 0 && t == 0) || (i == N && t == 1)
    decreases N - i
  {
    if s[i] != x {  // Op. interesante
      i := i+1 ;     
    } else {
      N := i;  // break;
    }
    t := t + 1;
  }
  assert t <= f(N);
  assert bigO(f, constGrowth()) by { var c, n0 := lem_fBigOconst(); }
} 

lemma lem_fBigOconst() returns (c:nat, n0:nat)
  ensures bigOfrom(c, n0, f, constGrowth())
{
  // we show that c=1 and n0=0
  c, n0 := 1, 0;
  forall n:nat | 0 <= n0 <= n
    ensures f(n) <= c*constGrowth()(n)
  {
    assert f(n) == 1;
    assert f(n) <= c*constGrowth()(n); 
  }
}