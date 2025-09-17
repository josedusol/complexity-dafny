include "../../../theory/math/Function.dfy"
include "../../../theory/math/LemFunction.dfy"
include "../../../theory/math/TypeR0.dfy"
include "../../../theory/Complexity/Asymptotics.dfy"

import opened Function
import opened LemFunction
import opened TypeR0
import opened Asymptotics

type Input {
  function size() : nat
}

ghost function f(N:nat) : nat
{ 
  N
}

method lin(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
  ensures tIsBigOh(x.size(), t as R0, linGrowth())
{
  var N := x.size();
  t := 0;

  var i := 0;
  while i != N
    invariant 0 <= i <= N
    invariant t == T(N,0) - T(N,i)   // = T(N, N-i)
    decreases N - i
  {
    // Op. interesante
    i := i+1 ;
    t := t+1 ;
  }

  assert t == T(N, 0); 
  assert t == f(N) by { lem_Tclosed(N, 0); }
  assert liftToR0(f) in O(linGrowth()) by { var c, n0 := lem_fBigOlin(); }
}

method linFor(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
  ensures tIsBigOh(x.size(), t as R0, linGrowth())
{
  var N := x.size();
  t := 0;
  
  for i := 0 to N
    invariant t == T(N,0) - T(N,i)   // = T(N, N-i)
  {
    // Op. interesante
    t := t+1 ;
  }

  assert t == T(N, 0); 
  assert t == f(N) by { lem_Tclosed(N, 0); }
  assert liftToR0(f) in O(linGrowth()) by { var c, n0 := lem_fBigOlin(); }
}

lemma lem_fBigOlin() returns (c:R0, n0:nat)
  ensures c > 0.0 && bigOhFrom(c, n0, liftToR0(f), linGrowth())
{
  c, n0 := 1.0, 0;
  forall n:nat | 0 <= n0 <= n
    ensures f(n) as R0 <= c*linGrowth()(n)
  {
    calc {
         f(n) as R0;
      == n as R0;
      <= c * n as R0;
      == c*linGrowth()(n);
    }
  }
}

ghost function T(N:nat, i:nat): nat
  requires 0 <= i <= N
  decreases N - i
{
  if i != N
  then T(N, i+1) + 1 
  else 0
}

lemma lem_Tclosed(N:nat, i:nat)
  requires 0 <= i <= N
  decreases N - i
  ensures T(N, i) == N - i
{  
}