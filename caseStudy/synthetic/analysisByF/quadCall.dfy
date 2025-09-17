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

ghost function f(n:nat) : nat
{
  n*n
}

method quadCall(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
  ensures tIsBigOh(x.size(), t as R0, quadGrowth())
{
  var N := x.size();
  t := 0;
  
  var i := 0;
  while i != N
    invariant 0 <= i <= N
    invariant t == T1(N,0) - T1(N,i)  // = T1(N, N-i)
    decreases N - i
  {
    var t' := quadCallSub(x);
    lem_T1closed(N, N-i); lem_T1closed(N, N-(i+1));
    i := i+1;
    t := t + t'; 
  }

  assert t == T1(N, 0); 
  assert t == f(N) by { lem_T1closed(N, 0); }
  assert liftToR0(f) in O(quadGrowth()) by { var c, n0 := lem_fBigOquad(); }
} 

ghost function f'(n:nat) : nat
{
  n
}

method quadCallSub(x:Input) returns (ghost t:nat)
  ensures t == f'(x.size())
  ensures tIsBigOh(x.size(), t as R0, linGrowth())
{
  var N := x.size();
  var i;
  i, t := 0, 0;
  while i != N
    invariant 0 <= i <= N
    invariant t == T2(N,0) - T2(N,i)  // = T1(N, N-i)
    decreases N - i
  {
    // Op. interesante
    i := i+1;
    t := t+1;
  }
  assert t == T2(N, 0); 
  assert t == f'(N) by { lem_T2closed(N, 0); }
  assert liftToR0(f') in O(linGrowth()) by { var c, n0 := lem_subBigOlin(); }
} 

ghost function T1(n:nat, i:nat): nat
  requires  0 <= i <= n
  decreases n - i
{
  if i != n 
  then T1(n, i+1) + T2(n, 0) 
  else 0
}

ghost function T2(n:nat, j:nat): nat
  requires  0 <= j <= n
  decreases n - j
{
  if j != n 
  then T2(n, j+1) + 1 
  else 0
}

lemma lem_T2closed(n:nat, j:nat)
  requires 0 <= j <= n
  decreases n - j
  ensures T2(n, j) == n - j
{  
  if j != n  { 
    lem_T2closed(n, j+1); 
  }  
}

lemma lem_T1closed(n:nat, i:nat)
  requires 0 <= i <= n
  decreases n - i
  ensures T1(n, i) == (n - i)*n
{  
  if i != n  { 
    lem_T2closed(n, 0);
    lem_T1closed(n, i+1); 
  } 
}

lemma lem_subBigOlin() returns (c:R0, n0:nat)
  ensures c > 0.0 && bigOhFrom(c, n0, liftToR0(f'), linGrowth())
{
  c, n0 := 1.0, 0;
  forall n:nat | 0 <= n0 <= n
    ensures f'(n) as R0 <= c*linGrowth()(n)
  {
    calc {
         f'(n) as R0;
      == n as R0;
      <= c * n as R0;
      == c*linGrowth()(n);
    }
  }
}

lemma lem_fBigOquad() returns (c:R0, n0:nat)
  ensures c > 0.0 && bigOhFrom(c, n0, liftToR0(f), quadGrowth())
{
  c, n0 := 1.0, 0;
  forall n:nat | 0 <= n0 <= n
    ensures f(n) as R0 <= c*quadGrowth()(n)
  {
    calc {
         f(n) as R0;
      == (n*n) as R0;
      <= c * (n*n) as R0;
      == c*quadGrowth()(n);
    }
  }
}