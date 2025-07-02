include "../theory/math/ExpReal.dfy"
include "../theory/math/LemFunction.dfy"
include "../theory/math/SumReal.dfy"
include "../theory/math/TypeR0.dfy"
include "../theory/ComplexityR0.dfy"
include "../theory/MasterLR.dfy"

import opened ExpReal
import opened LemFunction
import opened SumReal
import opened TypeR0
import opened ComplexityR0
import opened MasterLR

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

ghost method linearSearch<A>(s:seq<A>, x:A) returns (i:nat, t:nat)
  ensures post(s, x, i)
  ensures t == T(|s|)
  ensures bigO(liftToR0(T), n => pow(n as R0, 1.0))
{
  assume {:axiom} forall i :: 0 <= i < |s| ==> s[i] != x;  // worst case
  var N; reveal T();
  i, N, t := 0, |s|, 0;
  while i != N
    invariant inv(s, x, i, N)
    invariant t == T(|s|) - T(|s|-i)  // = T(N, N-i)
    decreases N - i
  {
    if s[i] != x {  // Op. interesante
      i := i+1 ;     
    } else {
      N := i;  // break;
    }
    t := t + 1;
  }
  assert t == T(|s|); 
  lem_TbigOlin();  
} 

opaque ghost function T(N:nat): nat
  decreases N
{
  if N <= 0
  then 0
  else T(N-1) + 1 
}

lemma lem_Tdef(n:nat)
  ensures n <= 0 ==> T(n) == 0
  ensures n >  0 ==> T(n) == 1*T(n-1) + 1
{
  reveal T();
}

lemma lem_TbigOlin()
  ensures bigO(liftToR0(T), n => pow(n as R0, 1.0))
{
  var a:nat       := 1;
  var b:nat       := 0;
  var c:R0        := 0.0;
  var s:nat       := 1;
  var k:R0        := 0.0;
  var T':nat->R0  := liftToR0(T);
  var w:nat->R0   := liftToR0(n => 1);

  assert b >= s-1;  
  forall n:nat 
    ensures T'(n) == TbodyLR(a, b, c, s, T', w, n)
  {
    reveal TbodyLR;
    lem_Tdef(n);
  }    
  assert bigO(w, n => pow(n as R0, k)) by {   
    // we show that c=1 and n0=1
    forall n:nat | 0 <= 1 <= n
      ensures w(n) <= 1.0*polyGrowth(k)(n)
    {
      assert pow(n as R0, k) == 1.0 by { lem_powZeroAll(); }
      assert w(n) <= 1.0*polyGrowth(k)(n); 
    }
    assert bigOfrom(1.0, 1, w, polyGrowth(k));
  } 
  thm_masterMethodLR(a, b, c, s, T', w, k);
}