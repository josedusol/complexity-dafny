include "../../../theory/math/LemFunction.dfy"
include "../../../theory/math/TypeR0.dfy"
include "../../../theory/ComplexityR0.dfy"

import opened LemFunction
import opened TypeR0
import opened ComplexityR0

type Input {
  function size() : nat
}

ghost function f(N:nat) : nat
{
  3*N
}

method lin3(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
  ensures tIsBigO(x.size(), t as R0, linGrowth())
{
  var N := x.size();

  var i, j;
  i, j, t := 0, 0, 0;
  while i != 3
    invariant 0 <= i <= 3
    invariant t == T1(N,0) - T1(N,i)  // = T1(N, N-i)
    decreases 3 - i
  {
    j := 0; ghost var t' := 0; 
    while j != N
      invariant 0 <= j <= N
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
  assert liftToR0(f) in O(linGrowth()) by { var c, n0 := lem_fBigOlin(); }
} 

method lin3For(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
  ensures tIsBigO(x.size(), t as R0, linGrowth())
{
  var N := x.size();
  t := 0;

  for i := 0 to 3
    invariant t == T1(N,0) - T1(N,i)   // = T(N, N-i)
  {
    ghost var t' := 0;
    for j := 0 to N
      invariant t' == T2(N,0) - T2(N,j)   // = T2(N, N - j)
    {
      // Op. interesante
      t' := t'+1;
    }
    t := t+t';
  }
  
  assert t == T1(N, 0); 
  assert t == f(N) by { lem_T1closed(N, 0); }
  assert liftToR0(f) in O(linGrowth()) by { var c, n0 := lem_fBigOlin(); }
}

ghost function T1(N:nat, i:nat): nat
  requires  0 <= i <= 3
  decreases 3 - i
{
  if i != 3
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
  requires 0 <= i <= 3
  decreases 3 - i
  ensures T1(N, i) == (3 - i)*N
{  
  if i != 3  { 
    lem_T2closed(N, 0);
    lem_T1closed(N, i+1); 
  } 
}

lemma lem_fBigOlin() returns (c:R0, n0:nat)
  ensures c > 0.0 && bigOfrom(c, n0, liftToR0(f), linGrowth())
{
  c, n0 := 3.0, 0;
  forall n:nat | 0 <= n0 <= n
    ensures f(n) as R0 <= c*linGrowth()(n)
  {
    calc {
         f(n) as R0;
      == (3*n) as R0;
         c*linGrowth()(n);  
    }
  }
}