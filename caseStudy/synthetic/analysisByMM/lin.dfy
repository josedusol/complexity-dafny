include "../../../theory/math/Function.dfy"
include "../../../theory/math/ExpReal.dfy"
include "../../../theory/math/LemFunction.dfy"
include "../../../theory/math/TypeR0.dfy"
include "../../../theory/Complexity/Asymptotics.dfy"
include "../../../theory/Complexity/MasterLR.dfy"

import opened ExpReal
import opened Function
import opened LemFunction
import opened TypeR0
import opened Asymptotics
import opened MasterLR

type Input {
  function size() : nat
}

method lin(x:Input) returns (ghost t:nat)
  ensures t == T(x.size())
  ensures liftToR0(T) in O(n => exp(n as R0, 1.0))
{
  var N := x.size();
  
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
  lem_TbigOlin();
} 

method linFor(x:Input) returns (ghost t:nat)
  ensures t == T(x.size())
  ensures liftToR0(T) in O(n => exp(n as R0, 1.0))
{
  var N := x.size();
  t := 0; reveal T();
  
  for i := 0 to N
    invariant t == T(N) - T(N-i)  // = T2(i)
  {
    // Op. interesante
    t := t+1 ;
  }

  assert t == T(N); 
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
  ensures liftToR0(T) in O(n => exp(n as R0, 1.0))
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
  assert w in O(n => exp(n as R0, k)) by {   
    // we show that c=1 and n0=1
    forall n:nat | 0 <= 1 <= n
      ensures w(n) <= 1.0*polyGrowth(k)(n)
    {
      assert exp(n as R0, k) == 1.0 by { lem_ZeroAuto(); }
      assert w(n) <= 1.0*polyGrowth(k)(n); 
    }
    assert bigOhFrom(1.0, 1, w, polyGrowth(k));
  } 
  thm_masterMethodLR(a, b, c, s, T', w, k);
}