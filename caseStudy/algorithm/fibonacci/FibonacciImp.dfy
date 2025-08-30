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
{
  var i, f1, f2 := 0, 0, 1;
  while (i < n)
    invariant 0 <= i <= n
    invariant f1 == fib(i)
    invariant f2 == fib(i+1)
  {
    var tmp := f1 + f2;
    f1 := f2;
    f2 := tmp;
    i := i + 1;
  }
  r := f1;
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

ghost function f(n:nat) : R0
{ 
  n as R0 
}

method FibT(n:nat) returns (r:nat, ghost t:R0)
  requires n >= 0
  ensures  r == fib(n)
  ensures  t == f(n)
  ensures  tIsBigO(n, t, linGrowth())
{
  t := 0.0; reveal T();
  var i, f1, f2 := 0, 0, 1;
  while i < n
    invariant 0 <= i <= n
    invariant f1 == fib(i)
    invariant f2 == fib(i+1)
    invariant t == T(i)              // = T(n)- T(i)
    invariant t == T2(n,0) - T2(n,i) // = T2(i)
    invariant t == i as R0
    decreases n - i
  {
    var tmp := f1 + f2;
    f1 := f2;
    f2 := tmp;
    i := i + 1;
    t := t + 1.0;
  }
  r := f1;
  assert t == n as R0; 
  assert f in O(linGrowth()) by { var c, n0 := lem_fBigOlin(); }
}

ghost function T(n:nat): R0
  decreases n
{
  if n == 0 then 0.0 else T(n-1) + 1.0
}

ghost function T2(N:nat, i:nat): R0
  requires 0 <= i <= N
  decreases N - i
{
  if i != N
  then T2(N, i+1) + 1.0
  else 0.0
}

lemma lem_fBigOlin() returns (c:R0, n0:nat)
  ensures c > 0.0 && bigOfrom(c, n0, f, linGrowth())
{
  c, n0 := 1.0, 1;
  forall n:nat | 0 <= n0 <= n
    ensures f(n) <= c*linGrowth()(n)
  {
    calc {
         f(n);
      == n as R0;
      == { lem_expOne(n as R0); }
         exp(n as R0, 1.0);
      <= c*exp(n as R0, 1.0); 
      == c*linGrowth()(n);  
    }
  }
}

method FibTtest() {
  ghost var t;
  var r;
  r, t := FibT(0); assert r == 0 && t == 0.0;
  r, t := FibT(1); assert r == 1 && t == 1.0;
  r, t := FibT(2); assert r == 1 && t == 2.0;
  r, t := FibT(3); assert r == 2 && t == 3.0;
  r, t := FibT(4); assert r == 3 && t == 4.0;
  r, t := FibT(5); assert r == 5 && t == 5.0;
  r, t := FibT(6); assert r == 8 && t == 6.0;
}