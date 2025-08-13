include "../theory/math/ExpReal.dfy"
include "../theory/math/LemFunction.dfy"
include "../theory/math/TypeR0.dfy"
include "../theory/ComplexityR0.dfy"
include "../theory/MasterLR.dfy"

import opened ExpReal
import opened LemFunction
import opened TypeR0
import opened ComplexityR0
import opened MasterLR

method quad(N:nat)
  returns (ghost t:nat, ghost t':nat)
  ensures t == T1(N, N)
  ensures liftToR0(n => T1(n,N)) in O(polyGrowth(2.0))
{
  var i, j; reveal T1(),T2();
  i, j, t, t' := 0, 0, 0, 0;
  while i != N
    invariant 0 <= i <= N
    invariant t == T1(N, N) - T1(N-i, N) // = T1'(i, N) 
    decreases N - i 
  {
    j := 0; t' := 0; 
    while j != N
      invariant 0 <= j <= N && i != N
      invariant t' == T2(N) - T2(N-j) // = T2'(j)
      decreases N - j
    {
      // Op. interesante
      j := j+1;
      t' := t'+1;
    }
    i := i+1;
    t := t+t';
  }
  assert t == T1(N, N); 
  lem_T1BigOquad(N);
} 

opaque ghost function T1(i:nat, N:nat): nat
  decreases i
{
  if i <= 0
  then 0
  else T1(i-1, N) + T2(N) 
}

opaque ghost function T2(j:nat): nat
  decreases j
{
  if j <= 0
  then 0
  else T2(j-1) + 1 
}

lemma lem_T1def(i:nat, N:nat)
  ensures i <= 0 ==> T1(i,N) == 0
  ensures i >  0 ==> T1(i,N) == 1*T1(i-1,N) + T2(N)
{
  reveal T1();
}

lemma lem_T2def(n:nat)
  ensures n <= 0 ==> T2(n) == 0
  ensures n >  0 ==> T2(n) == 1*T2(n-1) + 1
{
  reveal T2();
}

lemma lem_T1BigOquad(N:nat)
  ensures liftToR0(n => T1(n,N)) in O(n => exp(n as R0, 2.0))
{
  var a:nat       := 1;
  var b:nat       := 0;
  var c:R0        := 0.0;
  var s:nat       := 1;
  var k:R0        := 1.0;
  var T1':nat->R0 := liftToR0(n => T1(n,N));
  var w:nat->R0   := liftToR0(n => T2(N));

  assert b >= s-1; 
  forall n:nat 
    ensures T1'(n) == TbodyLR(a, b, c, s, T1', w, n)
  {
    reveal TbodyLR; 
    lem_T1def(n, N);
  } 
  assert w in O(n => exp(n as R0, k))
   by { lem_T1BigOquadAux(N); }
  thm_masterMethodLR(a, b, c, s, T1', w, k); 
}

lemma {:isolate_assertions} lem_T1BigOquadAux(N:nat)
  ensures liftToR0(n => T2(N)) in O(n => exp(n as R0, 1.0))
{
  var k:R0 := 1.0;
  var w:nat->R0 := liftToR0(n => T2(N)); 

  var c:R0 := T2(N) as R0;
  var n0:nat := 1; 
  forall n:nat | 0 <= 1 <= n
    ensures w(n) <= c * exp(n as R0, k) as R0
  {
    assert T2(N) as R0 <= c * n as R0
      by { assert T2(N) <= (T2(N))*n; }
    assert exp(n as R0, k) == n as R0 
      by { assert n as R0 > 0.0; lem_expOne(n as R0); }
    assert T2(N) as R0 <= c * exp(n as R0, k); 
    assert w(n) <= c * exp(n as R0, k)
      by { assert w(n) == T2(N) as R0; }
  }
  assert bigOfrom(c, n0, w, n => exp(n as R0, k));  
}

lemma lem_T2BigOlin()
  ensures liftToR0(T2) in O(n => exp(n as R0, 1.0))
{
  var a:nat       := 1;
  var b:nat       := 0;
  var c:R0        := 0.0;
  var s:nat       := 1;
  var k:R0        := 0.0;
  var T2':nat->R0 := liftToR0(T2);
  var w:nat->R0   := liftToR0(n => 1);

  forall n:nat 
    ensures T2'(n) == TbodyLR(a, b, c, s, T2', w, n)
  {
    reveal TbodyLR;
    lem_T2def(n);
  } 
  assert w in O(n => exp(n as R0, k)) by {   
    // we show that c=1 and n0=1
    forall n:nat | 0 <= 1 <= n
      ensures w(n) <= 1.0*polyGrowth(k)(n)
    {
      assert exp(n as R0, k) == 1.0 by { lem_expZeroAll(); }
      assert w(n) <= 1.0*polyGrowth(k)(n); 
    }
    assert bigOfrom(1.0, 1, w, polyGrowth(k));
  } 
  thm_masterMethodLR(a, b, c, s, T2', w, k);
}