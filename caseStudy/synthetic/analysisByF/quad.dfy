include "../../../theory/math/ExpNat.dfy"
include "../../../theory/ComplexityNat.dfy"

import opened ExpNat
import opened ComplexityNat

type Input {
  function size() : nat
}

ghost function f(N:nat) : nat
{
  exp(N,2)
}

method quad(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
  ensures tIsBigO(x.size(), t, quadGrowth())
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
  assert t == f(N) by { reveal exp(); lem_T1closed(N, 0); }
  assert t <= f(N); 
  assert f in O(quadGrowth()) by { var c, n0 := lem_fBigOquad(); }
} 

method quadFor(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
  ensures tIsBigO(x.size(), t, quadGrowth())
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
  assert t == f(N) by { reveal exp(); lem_T1closed(N, 0); }
  assert t <= f(N); 
  assert f in O(quadGrowth()) by { var c, n0 := lem_fBigOquad(); }
}

ghost function T1(N:nat, i:nat): nat
  requires  0 <= i <= N
  decreases N - i
{
  if i != N 
  then T1(N, i+1) + T2(N, 0) 
  else 0
}

ghost function T2(N:nat, j:nat): nat
  requires  0 <= j <= N
  decreases N - j
{
  if j != N 
  then T2(N, j+1) + 1 
  else 0
}

lemma lem_T2closed(N:nat, j:nat)
  requires 0 <= j <= N
  decreases N - j
  ensures T2(N, j) == N - j
{  
  if j != N  { 
    lem_T2closed(N, j+1); 
  }  
}

lemma lem_T1closed(N:nat, i:nat)
  requires 0 <= i <= N
  decreases N - i
  ensures T1(N, i) == (N - i)*N
{  
  if i != N  { 
    lem_T2closed(N, 0);
    lem_T1closed(N, i+1); 
  } 
}

lemma lem_fBigOquad() returns (c:nat, n0:nat)
  ensures c > 0 && bigOfrom(c, n0, f, quadGrowth())
{
  c, n0 := 1, 0;
  forall n:nat | 0 <= n0 <= n
    ensures f(n) <= c*quadGrowth()(n)
  {
    calc {
         f(n);
      == exp(n,2);
      == { reveal exp(); }
         n*n;   
    }
    assert f(n) <= c*quadGrowth()(n); 
  }
}