include "../../../theory/math/LemFunction.dfy"
include "../../../theory/math/SumReal.dfy"
include "../../../theory/math/TypeR0.dfy"
include "../../../theory/ComplexityNat.dfy"
include "./linearSearch.dfy"

import opened LemFunction
import opened SumReal
import opened TypeR0
import opened ComplexityNat

// Postcondition for a correct linear search algorithm
ghost function f1(N:nat) : nat
{
  0
}

ghost method linearSearchBT1<A>(s:seq<A>, x:A) returns (i:nat, t:nat)
  ensures post(s, x, i)
  ensures t == f1(|s|) 
  ensures tIsBigTh(|s|, t, constGrowth())
{
  assume {:axiom} |s| == 0;  // best case
  var n:nat;
  i, n, t := 0, |s|, 0;
  while i != n
    invariant inv(s, x, i, n)
    invariant i == 0 && t == 0
    decreases n - i
  {
    if s[i] != x {  // Op. interesante
      i := i+1 ;     
    } else {
      n := i;  // break;
    }
    t := t + 1;
  }
  assert t == f1(|s|);
  assert f1 in O(constGrowth())  by { var c, n0 := lem_f1BigOconst(); }
  assert f1 in Om(constGrowth()) by { var c, n0 := lem_f1BigOmconst(); }
} 

lemma lem_f1BigOconst() returns (c:nat, n0:nat)
  ensures bigOfrom(c, n0, f1, constGrowth())
{
  // we show that c=1 and n0=0
  c, n0 := 1, 0;
  forall n:nat | 0 <= n0 <= n
    ensures f1(n) <= c*constGrowth()(n)
  {
    assert f1(n) == 0;
    assert f1(n) <= c*constGrowth()(n); 
  }
}

lemma lem_f1BigOmconst() returns (c:nat, n0:nat)
  ensures bigOmFrom(c, n0, f1, constGrowth())
{
  // we show that c=1 and n0=0
  c, n0 := 0, 0;
  forall n:nat | 0 <= n0 <= n
    ensures c*constGrowth()(n) <= f1(n)
  {
    assert f1(n) == 0;
    assert c*constGrowth()(n) <= f1(n); 
  }
}

//**************************************************************************//

ghost function f2(N:nat) : nat
{
  1
}

ghost method linearSearchBT2<A>(s:seq<A>, x:A) returns (i:nat, t:nat)
  ensures post(s, x, i)
  ensures t == f2(|s|)
  ensures tIsBigTh(|s|, t, constGrowth())
{
  assume {:axiom} |s| > 0 && s[0] == x;  // best case when not empty
  var n:nat;
  i, n, t := 0, |s|, 0;
  while i != n
    invariant inv(s, x, i, n)
    invariant i < n  ==> t == 0
    invariant i == n ==> t == 1
    decreases n - i
  {
    if s[i] != x {  // Op. interesante
      i := i+1 ;     
    } else {
      n := i;  // break;
    }
    t := t + 1;
  }
  assert t == f2(|s|);
  assert f2 in O(constGrowth())  by { var c, n0 := lem_f2BigOconst(); }
  assert f2 in Om(constGrowth()) by { var c, n0 := lem_f2BigOmconst(); }
} 

lemma lem_f2BigOconst() returns (c:nat, n0:nat)
  ensures bigOfrom(c, n0, f2, constGrowth())
{
  c, n0 := 1, 0;
  forall n:nat | 0 <= n0 <= n
    ensures f2(n) <= c*constGrowth()(n)
  {
    assert f2(n) == 1;
    assert f2(n) <= c*constGrowth()(n); 
  }
}

lemma lem_f2BigOmconst() returns (c:nat, n0:nat)
  ensures bigOmFrom(c, n0, f2, constGrowth())
{
  c, n0 := 1, 0;
  forall n:nat | 0 <= n0 <= n
    ensures c*constGrowth()(n) <= f2(n) 
  {
    assert f2(n) == 1;
    assert c*constGrowth()(n) <= f2(n); 
  }
}