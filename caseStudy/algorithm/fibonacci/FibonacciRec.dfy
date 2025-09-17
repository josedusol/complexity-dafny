include "../../../theory/math/ExpReal.dfy"
include "../../../theory/math/LemBoundsReal.dfy"
include "../../../theory/math/Root2Real.dfy"
include "../../../theory/math/RootReal.dfy"
include "../../../theory/math/TypeR0.dfy"
include "../../../theory/Complexity/Asymptotics.dfy"
include "../../../theory/Complexity/LemBigOh.dfy"
include "../../../theory/Complexity/LemBigOm.dfy"
include "../../../theory/Complexity/MasterLR.dfy"

import opened ExpReal
import opened LemBoundsReal
import R2R = Root2Real
import RR  = RootReal
import opened TypeR0
import opened Asymptotics
import LOh = LemBigOh
import LOm = LemBigOm
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

// Counter t counts the number of recursive calls 
// This is exactly the edges of the recursion call tree
// It is known that t ∈ Θ(φ^n) where φ is the golden ratio.
// However, here we prove weaker bounds t ∈ O(2^n) and t ∈ Ω(2^(n/2)) = Ω(sqrt(2)^n)
method FibT(n:nat) returns (r:nat, ghost t:R0)
  requires n >= 0
  ensures  r == fib(n) && t == T(n)
  ensures  T in O(n => exp(2.0, n as R0))
  ensures  T in Om(n => exp(2.0, (n as R0)/2.0))
  ensures  tIsBigOh(n, t, expGrowth(2.0))
  decreases n
{
  if n < 2 {
    r, t := n, 0.0;
  } else {
    var a, t1 := FibT(n-1);
    var b, t2 := FibT(n-2);
    r, t := a + b, t1 + t2 + 2.0;
  }
  lem_TsandwichAsymp();
}

// Recurrence T characterizes counter t 
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

lemma lem_Tbounds(n:nat)
  requires n > 1
  ensures  2.0*T(n-2) + 2.0 <= T(n) <= 2.0*T(n-1) + 2.0
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
  forall n:nat | n > 1
    ensures 2.0*T(n-2) + 2.0 <= T(n)
  { 
    calc {
         T(n);
      == T(n-1) + T(n-2) + 2.0;
      >= { lem_TmonoIncr(n-1, n-2); }
         T(n-2) + T(n-2) + 2.0;
      == 2.0*T(n-2) + 2.0;
    }
  }  
}

opaque ghost function Tup(n:nat): R0
  decreases n
{
  match n
    case 0 => T(n)
    case 1 => T(n)
    case _ => 2.0*Tup(n-1) + 2.0
}

// Exact sol:
//   T(n) = (2^((n - 1)/2))((sqrt(2) - 1)(-1)^n + sqrt(2) + 1) - 2  
opaque ghost function Tlo(n:nat): R0
  decreases n
{
  match n
    case 0 => T(n)
    case 1 => T(n)
    case _ => 2.0*Tlo(n-2) + 2.0
}

lemma lem_Tsandwich(n:nat)
  ensures Tlo(n) <= T(n) <= Tup(n)
{
  reveal Tup();
  reveal Tlo();
  if n > 1 { 
    lem_Tbounds(n); 
    lem_Tsandwich(n-1);  
  }
}

lemma lem_TsandwichAuto()
  ensures forall n :: Tlo(n) <= T(n) <= Tup(n)
{
  forall n:nat 
    ensures Tlo(n) <= T(n) <= Tup(n)
  {
    lem_Tsandwich(n);
  }
}

lemma lem_TsandwichAsymp()
  ensures T in O(n  => exp(2.0, n as R0))
  ensures T in Om(n => exp(2.0, (n as R0)/2.0))
{
  assert T in O(n => exp(2.0, n as R0)) by {
    assert forall n :: n >= 0 ==> T(n) <= Tup(n) by { lem_TsandwichAuto(); }
    assert Tup in O(n => exp(2.0, n as R0)) by { lem_TupBigOexp2(); }
    LOh.lem_LEQdownwardClosure(T, Tup, (n => exp(2.0, n as R0)), 0);  
  }
  assert T in Om(n => exp(2.0, (n as R0)/2.0)) by {
    assert forall n :: n >= 0 ==> Tlo(n) <= T(n) by { lem_TsandwichAuto(); }
    assert Tlo in Om(n => exp(2.0, (n as R0)/2.0)) by { lem_TloBigOmSqrtExp2(); }
    LOm.lem_LEQupwardClosure(T, Tlo, n => exp(2.0, (n as R0)/2.0), 0);  
  }
}

lemma lem_TupDef(n:nat)
  ensures n <= 1 ==> Tup(n) == 0.0
  ensures n > 1  ==> Tup(n) == 2.0*Tup(n-1) + 2.0
{ 
  reveal Tup();
}

lemma lem_TloDef(n:nat)
  ensures n <= 1 ==> Tlo(n) == 0.0
  ensures n > 1  ==> Tlo(n) == 2.0*Tlo(n-2) + 2.0
{ 
  reveal Tlo();
}

lemma lem_TupBigOexp2()
  ensures Tup in O(n => exp(2.0, n as R0))
{
  var a:nat       := 2;
  var b:nat       := 1;
  var c:R0        := 0.0;
  var s:nat       := 1;
  var k:R0        := 0.0;
  var w:nat->R0   := n => 2.0;

  assert b >= s-1;  
  forall n:nat 
    ensures Tup(n) == TbodyLR(a, b, c, s, Tup, w, n)
  {
    reveal TbodyLR;
    lem_TupDef(n);
  }    
  assert w in O(n => exp(n as R0, k)) by {   
    // we show that c=2 and n0=1
    forall n:nat | 0 <= 1 <= n
      ensures w(n) <= 2.0*polyGrowth(k)(n)
    {
      assert exp(n as R0, k) == 1.0 by { lem_ZeroAuto(); }
      assert w(n) <= 2.0*polyGrowth(k)(n); 
    }
    assert bigOhFrom(2.0, 1, w, polyGrowth(k));
  } 
  thm_masterMethodLR(a, b, c, s, Tup, w, k);
  assert Tup in O(n => exp(n as R0, 0.0)*exp(2.0, n as R0 / 1.0));
  // simpl TODO
  assume Tup in O(n => exp(2.0, n as R0));
}

lemma {:isolate_assertions} lem_TloBigOmSqrtExp2()
  ensures Tlo in Om(n => exp(2.0, (n as R0)/2.0))
{
  var c:R0, n0 := 1.0/2.0, 2;
  forall n:nat | 0 <= n0 <= n
    ensures c*exp(2.0, (n as R0)/2.0) <= Tlo(n)
  {
    lem_TloClosedBound(n, c, n0);
  }    
  assert c > 0.0 && bigOmFrom(c, n0, Tlo, n => exp(2.0, (n as R0)/2.0));
} 

lemma lem_TloClosedBound(n:nat, c:R0, n0:nat)
  requires c == 1.0/2.0 && n0 == 2
  requires n >= n0
  ensures  c*exp(2.0, (n as R0)/2.0) <= Tlo(n)
  decreases n
{
  if n < 4 {
    // BC: n < 4
    if n == 2 {
      calc {
             c*exp(2.0, (2.0 as R0)/2.0) <= Tlo(2);
        <==> c*exp(2.0, 1.0) <= Tlo(2);
        <==> { reveal Tlo(); }
             c*exp(2.0, 1.0) <= 2.0;
        <==> { lem_One(2.0); } 
             c*2.0 <= 2.0;
        <==> 1.0 <= 2.0;    
        <==> true;       
      }      
    } else if n == 3 {
      calc {
             c*exp(2.0, (3.0 as R0)/2.0) <= Tlo(3);
        <==> { reveal Tlo(); }
             c*exp(2.0, 1.0 + (1.0/2.0)) <= 2.0;
        <==> { assert c*exp(2.0, 1.0 + (1.0/2.0)) == c*(exp(2.0, 1.0)*exp(2.0, 1.0/2.0))
                 by { lem_Product(2.0, 1.0, 1.0/2.0); } }
             c*(exp(2.0, 1.0)*exp(2.0, 1.0/2.0)) <= 2.0;
        <==> { lem_One(2.0); }
             c*2.0*exp(2.0, 1.0/2.0) <= 2.0;
        <==> exp(2.0, 1.0/2.0) <= 2.0;           
        <==> { reveal R2R.sqrt(), RR.root(); }
             R2R.sqrt(2.0) <= 2.0;
        <==> { lem_1LqSqrt2Lq2(); }
             true;     
      }      
    }
  } else {
    // Step. n >= 4
    //   IH: n >= 2 ==> c*2^((n-2)/2) <= Tlo(n-2)
    //    T: n >= 2 ==> c*2^(n/2) <= Tlo(n)
    calc { 
         Tlo(n);
      == { lem_TloDef(n); }
         2.0*Tlo(n-2) + 2.0; 
      >= { lem_TloClosedBound(n-2, c, n0); }  
         2.0*(c*exp(2.0, ((n-2) as R0)/2.0)) + 2.0; 
      >= 2.0*c*exp(2.0, ((n-2) as R0)/2.0);
      == 2.0*c*exp(2.0, ((n as R0)/2.0) + -1.0);
      == { lem_Product(2.0, (n as R0)/2.0, -1.0); }
         2.0*c*exp(2.0, (n as R0)/2.0)*exp(2.0, -1.0);
      == { lem_Positive(2.0, 1.0); lem_Reciprocal(2.0, 1.0); }
         2.0*c*exp(2.0, (n as R0)/2.0)*(1.0 / exp(2.0, 1.0));
      == { lem_One(2.0); } 
         2.0*c*exp(2.0, (n as R0)/2.0)*(1.0/2.0);
      == c*exp(2.0, (n as R0)/2.0);         
    }
  }
}

method FibTtest() {
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