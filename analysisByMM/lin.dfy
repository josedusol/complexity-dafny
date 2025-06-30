include "../theory/math/ExpReal.dfy"
include "../theory/math/LemFunction.dfy"
include "../theory/math/TypeR0.dfy"
include "../theory/ComplexityR0.dfy"
include "../theory/GrowthRatesR0.dfy"
include "../theory/MasterLR.dfy"

import opened ExpReal
import opened LemFunction
import opened TypeR0
import opened ComplexityR0
import opened GrowthRatesR0
import opened MasterLR

method lin(N:nat) 
  returns (ghost t:nat)
  ensures t == T(N)
  ensures bigO(liftToR0(T), n => pow(n as R0, 1.0))
{
  var i; reveal T();
  i, t := 0, 0;
  while i != N
    invariant 0 <= i <= N
    invariant t == T(N) - T(N-i)  // = T2(i) 
    decreases N - i
  {
    // Op. interesante
    i := i+1 ; 
    t := t+1 ;
  }
  assert t == T(N); 
  lem_T2BigOlin();
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

lemma lem_T2BigOlin()
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