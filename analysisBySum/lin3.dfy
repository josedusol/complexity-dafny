include "../theory/math/ExpNat.dfy"
include "../theory/math/SumInt.dfy"
include "../theory/ComplexityNat.dfy"

import opened ExpNat
import opened SumInt
import opened ComplexityNat

ghost function f(N:nat) : nat
{
  3*pow(N,1)
}

method lin(N:nat)
  returns (ghost t:nat, ghost t':nat)
  ensures t == f(N)
  ensures tIsBigO(N, t, linGrowth())
{
  var i, j; reveal sum(); 
  i, j, t, t' := 0, 0, 0, 0;
  while i != 3
      invariant 0 <= i <= 3
      invariant t == sum(1, i, k => sum(1, N, k' => 1))
      decreases 3 - i
  {
    j := 0; t' := 0;
    while j != N
      invariant 0 <= j <= N
      invariant t' == sum(1, j, k' => 1)
      decreases N - j
    {
      // Op. interesante
      lem_sum_dropLastAll(1, j); 
      j := j+1 ;
      t' := t'+1 ;
    }
    lem_sum_dropLastAll(1, i);
    i := i+1 ;
    t := t+t' ;
  }
  assert t == sum(1, 3, k => sum(1, N, k' => 1)); 
  assert t == f(N) by { reveal pow(); lem_sum_constAll(1, N); }
  assert t <= f(N);
 
  assert bigO(f, linGrowth()) by { var c, n0 := lem_fBigOlin(); }
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