include "../../../theory/math/LemFunction.dfy"
include "../../../theory/math/SumReal.dfy"
include "../../../theory/math/TypeR0.dfy"
include "../../../theory/Complexity.dfy"
include "../../../theory/LemComplexityBigOh.dfy"
include "../../../theory/LemComplexityBigOm.dfy"
include "../../../theory/LemComplexityBigTh.dfy"
include "./linearSearch.dfy"

import opened LemFunction
import opened SumReal
import opened TypeR0
import opened Complexity
import opened LemComplexityBigOh
import opened LemComplexityBigTh

ghost function f1(N:nat) : nat
{
  0
}

ghost method linearSearchBT1<A>(s:seq<A>, x:A) returns (i:nat, t:nat)
  ensures post(s, x, i)
  ensures t == f1(|s|) 
  ensures tIsBigTh(|s|, t as R0, zeroGrowth())
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
  assert liftToR0(f1) in Th(zeroGrowth()) by {
      lem_bigTh_zeroGrowth(liftToR0(f1)) 
        by { assert 0 as R0 == 0.0; }
    }
  lem_bigTh_tIsBigTh2(|s|, t as R0, zeroGrowth());
} 

//**************************************************************************//

ghost function f2(N:nat) : nat
{
  1
}

ghost method linearSearchBT2<A>(s:seq<A>, x:A) returns (i:nat, t:nat)
  ensures post(s, x, i)
  ensures t == f2(|s|)
  ensures tIsBigTh(|s|, t as R0, constGrowth())
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
  assert liftToR0(f2) in Th(constGrowth()) by { 
      lem_bigTh_constGrowth(liftToR0(f2), 1.0)
        by { assert 1 as R0 == 1.0; }  
    }
  lem_bigTh_tIsBigTh2(|s|, t as R0, constGrowth());
}