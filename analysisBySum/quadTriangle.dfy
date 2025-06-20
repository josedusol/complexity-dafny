
include "../theory/complexity.dfy"

ghost function f(N:nat) : nat
{
  (N*(N+1))/2
}

method quadTriangle(N:nat)
  returns (ghost t:nat, ghost t':nat)
  ensures t == f(N)
  ensures tIsBigO(N, t, quadGrowth())
{
  var i, j; reveal sum();
  i, j, t, t' := 0, 0, 0, 0;
  while i != N
    invariant 0 <= i <= N
    invariant t == sum(1, i, k => sum(k, N, k' => 1))
    decreases N - i
  {
    j := i; t' := 0;
    while j != N
      invariant i <= j <= N
      invariant t' == sum(i+1, j, k' => 1)
      decreases N - j
    {
      // Op. interesante
      lem_sumDropLastAll(i+1,j);
      j := j+1 ;
      t' := t'+1 ;
    }
    lem_sumDropLastAll(1,i);
    i := i+1 ;
    t := t+t' ;
  }
  assert t == sum(1, N, k => sum(k, N, k' => 1));
  assert t == f(N) by { lem_solveSum(1, N, 1); } 
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
      == (n*(n+1))/2; 
      <= n*n;   
    }
    assert f(n) <= c*quadGrowth()(n) 
      by { reveal pow(); } 
  }
}

lemma lem_solveSum(i:nat, N:nat, c:nat)
  requires 0 <= i <= N+1
  ensures sum(1, N, k => sum(k, N, k' => 1)) == (N*(N+1))/2 
{
  calc {
       sum(1, N, k => sum(k, N, k' => 1));
    == { lem_solveInnerSum(1, N, 1); }
       sum(1, N, k => 1*(N-k+1));
    == { lem_sumLeibniz(1, N, k => 1*(N-k+1),
                              k => N-k+1); }
       sum(1, N, k => (N-k+1));
    == { lem_sumReverseIndex(1, N); }
       sum(1, N, k => k); 
    == { lem_sumTriangle(N); }  
       (N*(N+1))/2; 
  }
} 

lemma lem_solveInnerSum(i:nat, N:nat, c:nat)
  requires 0 <= i <= N+1
  decreases N - i
  ensures    sum(i, N, k => sum(k, N, k' => c)) 
          == sum(i, N, k => c*(N-k+1))
{ 
  if i == N+1 {   
    // BC: i > N
    calc {
        sum(N+1, N, k => sum(k, N, k' => c));
      == { assert N+1 > N; reveal sum(); } 
        0;
      == { assert N+1 > N; reveal sum(); } 
        sum(N+1, N, k => c*(N-k+1)); 
    }
  } else {  
    // Step. i <= N
    //   IH: sum(i+1, N, k => sum(k, N, k' => c)) = sum(i+1, N, k => c*(N-k+1) )
    //    T: sum(i, N, k => sum(k, N, k' => c))   = sum(i, N, k => c*(N-k+1) )
    calc {  
         sum(i, N, k => sum(k, N, k' => c));
      == { reveal sum(); }
         sum(i, N, k => c) + sum(i+1, N, k => sum(k, N, k' => c));
      == { lem_solveInnerSum(i+1, N, c); }  // by IH
         sum(i, N, k => c) + sum(i+1, N, k => c*(N-k+1));
      == { lem_sumOverConstAll(i, N); } 
         c*(N-i+1) + sum(i+1, N, k => c*(N-k+1));      
      == { reveal sum(); }      
         sum(i, N, k => c*(N-k+1));           
    }  
  } 
}

//**************************************************************************//

ghost method testSum() { 
  reveal sum();
  var N:nat := 0;
  var r := sum(1, N, k => if 1<=k<=N then (N-k+1) else 0);
  assert r == 0; 
  assert (N*(N+1))/2 == 0; 

  N := 1;
  r := sum(1, N, k => if 1<=k<=N then (N-k+1) else 0); 
  assert r == 1;
  assert (N*(N+1))/2 == 1;

  N := 2;
  r := sum(1, N, k => if 1<=k<=N then (N-k+1) else 0); 
  assert r == 3; 
  assert (N*(N+1))/2 == 3;

  N := 3; 
  r := sum(1, N, k => if 1<=k<=N then (N-k+1) else 0); 
  assert r == 6;
  assert (N*(N+1))/2 == 6;

//   n := 4;
//   r := T1([1,2,3,4], n);
//   assert r == 10;
//   assert (n*(n+1))/2 == 10;
} 