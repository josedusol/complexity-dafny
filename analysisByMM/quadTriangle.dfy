include "../theory/math/ExpReal.dfy"
include "../theory/math/Misc.dfy"
include "../theory/math/TypeR0.dfy"
include "../theory/ComplexityR0.dfy"
include "../theory/GrowthRatesR0.dfy"
include "../theory/MasterLR.dfy"

import opened ExpReal
import opened Misc
import opened TypeR0
import opened ComplexityR0
import opened GrowthRatesR0
import opened MasterLR

method quadTriangle(N:nat)
  returns (ghost t:nat, ghost t':nat)
  ensures t == T1(N)
  ensures bigOR0(liftToR0(T1), n => powr(n as R0, 2.0))
{
  var i, j; reveal T1(),T2();
  i, j, t, t' := 0, 0, 0, 0;
  while i != N
    invariant 0 <= i <= N
    invariant t == T1(N) - T1(N-i)
    decreases N - i
  {
    j := i; t' := 0; 
    while j != N
      invariant i <= j <= N && i != N
      invariant t' == T2(N-i) - T2(N-j)
      decreases N - j
    {
      // Op. interesante
      j  := j+1;
      t' := t'+1;
    }
    i := i+1;
    t := t+t';
  }
  assert t == T1(N); 
  lem_T1BigOquad();
} 

opaque ghost function T1(i:nat): nat
  decreases i
{
  if i <= 0
  then 0
  else T1(i-1) + T2(i) 
}

opaque ghost function T2(j:nat): nat
  decreases j
{
  if j <= 0
  then 0
  else T2(j-1) + 1 
}

lemma lem_T1def(i:nat)
  ensures i <= 0 ==> T1(i) == 0
  ensures i >  0 ==> T1(i) == 1*T1(i-1) + T2(i)
{
  reveal T1();
}

lemma lem_T2def(n:nat)
  ensures n <= 0 ==> T2(n) == 0
  ensures n >  0 ==> T2(n) == 1*T2(n-1) + 1
{
  reveal T2();
}

lemma lem_T1BigOquad() 
  ensures bigOR0(liftToR0(T1), n => powr(n as R0, 2.0))
{
  var a:nat       := 1;
  var b:nat       := 0;
  var c:R0        := 0.0;
  var s:nat       := 1;
  var k:R0        := 1.0;
  var T1':nat->R0 := liftToR0(T1);
  var w:nat->R0   := liftToR0(T2);

  assert b >= s-1;
  forall n:nat 
    ensures T1'(n) == TbodyLR(a, b, c, s, T1', w, n)
  {
    reveal TbodyLR; 
    lem_T1def(n);
  } 
  assert bigOR0(w, n => powr(n as R0, k)) by {   
    lem_T2BigOlin();
  } 
  thm_masterMethodLR(a, b, c, s, T1', w, k);
}

lemma lem_T2BigOlin()
  ensures bigOR0(liftToR0(T2), n => powr(n as R0, 1.0))
{
  var a:nat       := 1;
  var b:nat       := 0;
  var c:R0        := 0.0;
  var s:nat       := 1;
  var k:R0        := 0.0;
  var T2':nat->R0 := liftToR0(T2);
  var w:nat->R0   := liftToR0(n => 1);

  assert b >= s-1;  
  forall n:nat 
    ensures T2'(n) == TbodyLR(a, b, c, s, T2', w, n)
  {
    reveal TbodyLR;
    lem_T2def(n);
  }  
  assert bigOR0(w, n => powr(n as R0, k)) by {   
    // we show that c=1 and n0=1
    forall n:nat | 0 <= 1 <= n
      ensures w(n) <= 1.0*polyGrowthR0(k)(n)
    {
      assert powr(n as R0, k) == 1.0 by { lem_powrZeroAll(); }
      assert w(n) <= 1.0*polyGrowthR0(k)(n); 
    }
    assert bigOR0from(1.0, 1, w, polyGrowthR0(k));
  } 
  thm_masterMethodLR(a, b, c, s, T2', w, k);
}