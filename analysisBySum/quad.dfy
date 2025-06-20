
include "../theory/complexity.dfy"

ghost function f(N:nat) : nat
{
  pow(N,2)
}

method quad(N:nat)
  returns (ghost t:nat, ghost t':nat)
  ensures t == f(N)
  ensures tIsBigO(N, t, quadGrowth())
{
  var i, j; reveal sum();
  i, j, t, t' := 0, 0, 0, 0;
  while i != N
      invariant 0 <= i <= N
      invariant t == sum(1, i, k => sum(1, N, k' => 1))
      decreases N - i
  {
    j := 0; t' := 0;
    while j != N
      invariant 0 <= j <= N
      invariant t' == sum(1, j, k' => 1)
      decreases N - j
    {
      // Op. interesante
      lem_sumDropLastAll(1, j); 
      j := j+1 ;
      t' := t'+1 ;
    }
    lem_sumDropLastAll(1, i);
    i := i+1 ;
    t := t+t' ;
  }
  assert t == sum(1, N, k => sum(1, N, k' => 1)); 
  assert t == f(N) by { reveal pow(); lem_sumOverConstAll(1, N); }
  assert t <= f(N);
 
  assert bigO(f, quadGrowth()) by { var c, n0 := lem_fBigOquad(); }
} 

lemma lem_fBigOquad() returns (c:nat, n0:nat)
  ensures bigOfrom(c, n0, f, quadGrowth())
{
  // we show that c=1 and n0=0
  c, n0 := 1, 0;
  forall n:nat | 0 <= n0 <= n
    ensures f(n) <= c*quadGrowth()(n)
  {
    calc {
         f(n); 
      ==
         pow(n,2);
      == { reveal pow(); }
         n*n;   
    }
    assert f(n) <= c*quadGrowth()(n); 
  }
}