 
include "../theory/complexity.dfy"

ghost function f(N:nat) : nat
{
  if N < 10 then pow(N,1) else 20 
}

method linAfter(N:nat)
  returns (ghost t:nat)
  ensures t == f(N)
  ensures tIsBigO(N, t, constGrowth())
{
  reveal sum();
  if N < 10 {
    var i;
    i, t := 0, 0;
    while i != N
      invariant 0 <= i <= N
      invariant t == sum(1, i, x => 1)
      decreases N - i
    {
      // Op. interesante
      lem_sum_dropLastAll(1, i); 
      i := i+1 ;
      t := t+1 ;
    }     
  } else {
    // Op. interesante ocurre 20 veces
    t := 20 ;
  }
  assert t == if N < 10 then sum(1, N, k => 1) else 20; 
  assert t == f(N) by { reveal pow(); lem_sum_constAll(1, N); }
  assert t <= f(N);
 
  assert bigO(f, constGrowth()) by { var c, n0 := lem_fBigOconst(); }
} 

lemma lem_fBigOconst() returns (c:nat, n0:nat)
  ensures bigOfrom(c, n0, f, constGrowth())
{
  // we show that c=20 and n0=10
  c, n0 := 20, 10; 
  forall n:nat | 0 <= n0 <= n
    ensures f(n) <= c*constGrowth()(n)
  {
    calc {
         f(n);
      ==
         if n < 10 then pow(n,1) else 20;
      == { reveal pow(); }
         if n < 10 then n else 20;    
    }
    assert f(n) <= c*constGrowth()(n);
  }
}