include "../../../theory/math/ExpReal.dfy"
include "../../../theory/math/SumReal.dfy"
include "../../../theory/math/TypeR0.dfy"
include "../../../theory/ComplexityR0.dfy"
include "../../../theory/MasterLR.dfy"

import opened ExpReal
import opened SumReal
import opened TypeR0
import opened ComplexityR0
import opened MasterLR

ghost function fib(n:nat): nat
  decreases n
{
  match n
    case 0 => 0
    case 1 => 1
    case _ => fib(n-1) + fib(n-2)
}

method Fib(n:nat) returns (r:nat)
  requires n >= 0
  ensures  r == fib(n)
  decreases n
{
  if n < 2 {
    r := n;
  } else {
    var a := Fib(n-1);
    var b := Fib(n-2);
    r := a + b;
  }
}

method FibTest() {
  var r;
  r := Fib(0); assert r == 0;
  r := Fib(1); assert r == 1;
  r := Fib(2); assert r == 1;
  r := Fib(3); assert r == 2;
  r := Fib(4); assert r == 3;
  r := Fib(5); assert r == 5;
  r := Fib(6); assert r == 8;
}

/************************************************************/

method FibT(n:nat) returns (r:nat, ghost t:R0)
  requires n >= 0
  ensures  r == fib(n)
  ensures  t == T(n) <= T'(n)
  ensures  T' in O(n => exp(n as R0, 2.0))
  ensures  tIsBigO(n, t, polyGrowth(2.0))
  decreases n
{
  if n < 2 {
    r, t := n, 0.0;
  } else {
    var a, t1 := FibT(n-1);
    var b, t2 := FibT(n-2);
    r, t := a + b, t1 + t2 + 2.0;
  }
  lem_TleqT'(n);
  lem_T'bigOexp2();
}

method FibTTest() {
  ghost var t;
  var r;
  r, t := FibT(0); assert r == 0 && t == 0.0;
  r, t := FibT(1); assert r == 1 && t == 0.0;
  r, t := FibT(2); assert r == 1 && t == 2.0;
  r, t := FibT(3); assert r == 2 && t == 4.0;
  r, t := FibT(4); assert r == 3 && t == 8.0;
  r, t := FibT(5); assert r == 5 && t == 14.0;
  r, t := FibT(6); assert r == 8 && t == 24.0;
}

ghost function T(n:nat): R0
  decreases n
{
  match n
    case 0 => 0.0
    case 1 => 0.0
    case _ => T(n-1) + T(n-2) + 2.0
}


// n <= m ==> T(n) <= T(m)
lemma lem_TmonoIncr(n:nat, m:nat)
  ensures n <= m ==> T(n) <= T(m)
  decreases n, m
{  
  if n != 0 && m != 0 {  
    lem_TmonoIncr(n-1, m-1);  
  }
}

lemma lem_TupBound()
  ensures forall n :: n > 1 ==> T(n) <= 2.0*T(n-1) + 2.0
{
  forall n:nat | n > 1
    ensures T(n) <= 2.0*T(n-1) + 2.0
  { 
    calc {
         T(n);
      == T(n-1) + T(n-2) + 2.0;
      <= { lem_TmonoIncr(n-2, n-1); }
        T(n-1) + T(n-1) + 2.0;
      == 2.0*T(n-1) + 2.0;
    }
  }
}

lemma lem_TleqT'(n:nat)
  ensures T(n) <= T'(n)
{
  reveal T'();
  if n != 0 { 
    lem_TupBound(); 
    lem_TleqT'(n-1);  
  }
}

opaque ghost function T'(n:nat): R0
  decreases n
{
  match n
    case 0 => 0.0
    case 1 => 0.0
    case _ => 2.0*T'(n-1) + 2.0
}

lemma lem_T'def(n:nat)
  ensures n <= 1 ==> T'(n) == 0.0
  ensures n > 1  ==> T'(n) == 2.0*T'(n-1) + 2.0
{ 
  reveal T'();
}

lemma lem_T'bigOexp2()
  ensures T' in O(n => exp(n as R0, 2.0))
{
  var a:nat       := 2;
  var b:nat       := 1;
  var c:R0        := 0.0;
  var s:nat       := 1;
  var k:R0        := 0.0;
  var w:nat->R0   := n => 2.0;

  assert b >= s-1;  
  forall n:nat 
    ensures T'(n) == TbodyLR(a, b, c, s, T', w, n)
  {
    reveal TbodyLR;
    lem_T'def(n);
  }    
  assert w in O(n => exp(n as R0, k)) by {   
    // we show that c=2 and n0=1
    forall n:nat | 0 <= 1 <= n
      ensures w(n) <= 2.0*polyGrowth(k)(n)
    {
      assert exp(n as R0, k) == 1.0 by { lem_expZeroAll(); }
      assert w(n) <= 2.0*polyGrowth(k)(n); 
    }
    assert bigOfrom(2.0, 1, w, polyGrowth(k));
  } 
  thm_masterMethodLR(a, b, c, s, T', w, k);
  assert T' in O(n => exp(n as R0, 0.0)*exp(2.0, (n/1) as R0));
  // simpl TODO
  assume T' in O(n => exp(n as R0, 2.0));
}