include "../../../theory/math/LemFunction.dfy"
include "../../../theory/math/TypeR0.dfy"
include "../../../theory/Complexity.dfy"

import opened LemFunction
import opened TypeR0
import opened Complexity

type Input {
  function size() : nat
}

ghost function f(n:nat) : nat
{
  n*n
}

method quad(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
  ensures tIsBigO(x.size(), t as R0, quadGrowth())
{
  var N := x.size();
  t := 0;

  var i, j;
  i, j := 0, 0;
  while i != N
    invariant 0 <= i <= N
    invariant t == T1(N,0) - T1(N,i)  // = T1(N, N-i)
    decreases N - i
  {
    j := 0; ghost var t' := 0; 
    while j != N
      invariant 0 <= j <= N && i != N
      invariant t' == T2(N,0) - T2(N,j)  // = T2(N, N - j)
      decreases N - j
    {
      // Op. interesante
      j := j+1;
      t' := t'+1;
    }
    i := i+1;
    t := t+t';
  }

  assert t == T1(N, 0); 
  assert t == f(N) by { lem_T1closed(N, 0); }
  assert liftToR0(f) in O(quadGrowth()) by { var c, n0 := lem_fBigOquad(); }
} 

method quadFor(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
  ensures tIsBigO(x.size(), t as R0, quadGrowth())
{
  var N := x.size();
  t := 0;

  for i := 0 to N
    invariant t == T1(N,0) - T1(N,i)  // = T1(N, N-i)
  {
    ghost var t' := 0;
    for j := 0 to N
      invariant t' == T2(N,0) - T2(N,j)  // = T2(N, N - j)
    {
      // Op. interesante
      t' := t'+1;
    }
    t := t+t';
  }
  
  assert t == T1(N, 0); 
  assert t == f(N) by { lem_T1closed(N, 0); }
  assert liftToR0(f) in O(quadGrowth()) by { var c, n0 := lem_fBigOquad(); }
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

lemma lem_fBigOquad() returns (c:R0, n0:nat)
  ensures c > 0.0 && bigOfrom(c, n0, liftToR0(f), quadGrowth())
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