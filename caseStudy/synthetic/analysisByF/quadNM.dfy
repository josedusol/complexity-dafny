include "../../../theory/math/ExpNat.dfy"
include "../../../theory/ComplexityNat.dfy"

import opened ExpNat
import opened ComplexityNat

type Input {
  function size() : nat
}

ghost function f(N:nat, M:nat) : nat
{
  N*M
}

method quadNM(x:Input, y:Input) returns (ghost t:nat, ghost t':nat)
  ensures t == f(x.size(), y.size())
  ensures x.size() == y.size() ==> tIsBigO(x.size(), t, quadGrowth())
{
  var N, M := x.size(), y.size();
  var i, j;
  i, j, t, t' := 0, 0, 0, 0;
  while i != N
    invariant 0 <= i <= N
    invariant t == T1(N,M,0) - T1(N,M,i)  // = T1(N, N-i)
    decreases N - i
  {
    j := 0; t' := 0; 
    while j != M
      invariant 0 <= j <= M && i != N
      invariant t' == T2(N,M,0) - T2(N,M,j)  // = T2(N, N - j)
      decreases M - j
    {
      // Op. interesante
      j := j+1;
      t' := t'+1;
    }
    i := i+1;
    t := t+t';
  }
  assert t == T1(N,M,0); 
  assert t == f(N,M) by { lem_T1closed(N, M, 0); }
  assert t <= f(N,M); 
 
  assert N == M ==> t == (n => f(n,n))(N);
  assert (n => f(n,n)) in O(quadGrowth()) by { var c, n0 := lem_fBigOquad(); }
} 

ghost function T1(N:nat, M:nat, i:nat): nat
  requires  0 <= i <= N
  decreases N - i
{
  if i != N 
  then T1(N, M, i+1) + T2(N, M, 0) 
  else 0
}

ghost function T2(N:nat, M:nat, j:nat): nat
  requires  0 <= j <= M
  decreases M - j
{
  if j != M 
  then T2(N, M, j+1) + 1 
  else 0
}

lemma lem_T2closed(N:nat, M:nat, j:nat)
  requires 0 <= j <= M
  decreases M - j
  ensures T2(N, M, j) == M - j
{  
  if j != M  { 
    lem_T2closed(N, M, j+1); 
  }  
}

lemma lem_T1closed(N:nat, M:nat, i:nat)
  requires 0 <= i <= N
  decreases N - i
  ensures T1(N, M, i) == (N - i)*M
{  
  if i != N  { 
    lem_T2closed(N, M, 0);
    lem_T1closed(N, M, i+1); 
  } 
}

lemma lem_fBigOquad() returns (c:nat, n0:nat)
  ensures bigOfrom(c, n0, n => f(n,n), quadGrowth())
{
  c, n0 := 1, 0;
  forall n:nat | 0 <= n0 <= n
    ensures f(n,n) <= c*quadGrowth()(n)
  {
    calc {
         f(n,n);
      == n*n;  
      == { reveal exp(); }
         exp(n,2); 
    }
    assert n >= n0 ==> f(n,n) <= c*quadGrowth()(n); 
  }
}