include "../../../theory/math/ExpReal.dfy"
include "../../../theory/math/LemFunction.dfy"
include "../../../theory/math/TypeR0.dfy"
include "../../../theory/Complexity.dfy"
include "../../../theory/MasterLR.dfy"

import opened ExpReal
import opened LemFunction
import opened TypeR0
import opened Complexity
import opened MasterLR

type Input {
  function size() : nat
}

method quadTriangle(x:Input) returns (ghost t:nat, ghost t':nat)
  ensures t == T1(x.size())
  ensures liftToR0(T1) in O(n => exp(n as R0, 2.0))
{
  var N := x.size();
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

method quadTriangleFor(x:Input) returns (ghost t:nat)
  ensures t == T1(x.size())
  ensures liftToR0(T1) in O(n => exp(n as R0, 2.0))
{
  var N := x.size();
  t := 0; reveal T1(),T2();

  for i := 0 to N
    invariant t == T1(N) - T1(N-i)
  {
    ghost var t' := 0;
    for j := i to N
      invariant t' == T2(N-i) - T2(N-j)
    {
      // Op. interesante
      t' := t'+1;
    }
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
  ensures liftToR0(T1) in O(n => exp(n as R0, 2.0)) 
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
  assert w in O(n => exp(n as R0, k)) by {   
    lem_T2BigOlin();
  } 
  thm_masterMethodLR(a, b, c, s, T1', w, k);
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

  assert b >= s-1;  
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
      assert exp(n as R0, k) == 1.0 by { lem_exp_ZeroAuto(); }
      assert w(n) <= 1.0*polyGrowth(k)(n); 
    }
    assert bigOfrom(1.0, 1, w, polyGrowth(k));
  } 
  thm_masterMethodLR(a, b, c, s, T2', w, k);
}