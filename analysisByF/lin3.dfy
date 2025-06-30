include "../theory/math/ExpNat.dfy"
include "../theory/ComplexityNat.dfy"
include "../theory/GrowthRatesNat.dfy"

import opened ExpNat
import opened ComplexityNat
import opened GrowthRatesNat

ghost function f(N:nat) : nat
{
  3*pow(N,1)
}

method lin3(N:nat)
  returns (ghost t:nat, ghost t':nat)
  ensures t == f(N)
  ensures tIsBigO(N, t, linGrowth())
{
  var i, j;
  i, j, t, t' := 0, 0, 0, 0;
  while i != 3
    invariant 0 <= i <= 3
    invariant t == T1(N,0) - T1(N,i)  // = T1(N, N-i)
    decreases 3 - i
  {
    j := 0; t' := 0; 
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
  assert t == f(N) by { reveal pow(); lem_T1closed(N, 0); }
  assert t <= f(N); 
 
  assert bigO(f, linGrowth()) by { var c, n0 := lem_fBigOlin(); }
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

lemma lem_fBigOlin() returns (c:nat, n0:nat)
  ensures bigOfrom(c, n0, f, linGrowth())
{
  // we show that c=3 and n0=0
  c, n0 := 3, 0;
  forall n:nat | 0 <= n0 <= n
    ensures f(n) <= c*linGrowth()(n)
  {
    calc {
        f(n);
      ==
        3*pow(n,1);
      == { reveal pow(); }
        3*n;   
    }
    assert n >= n0 ==> f(n) <= c*linGrowth()(n); 
  }
}