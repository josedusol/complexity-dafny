
include "../theory/complexity.dfy"
include "../theory/mathSum.dfy"

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
      lem_sum_dropLastAll(i+1,j);
      j := j+1 ;
      t' := t'+1 ;
    }
    lem_sum_dropLastAll(1,i);
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
       sum(1, N, k => if 1<=k<=N then 1*(N-k+1) else 0);
    == { lem_sum_leibniz(1, N, k => if 1<=k<=N then 1*(N-k+1) else 0,
                              k => if 1<=k<=N then N-k+1 else 0); }
       sum(1, N, k => if 1<=k<=N then (N-k+1) else 0);
    == { lem_sumReverseIndexAux(1, N); }
       sum(1, N, k => k);
    == { lem_sum_triangle(N); }  
       (N*(N+1))/2; 
  }
}

// i <= j+1 ==> sum_{k=i}^{j}(j-k+i) = sum_{k=i}^{j}k
lemma {:axiom} lem_sumReverseIndexAux(i:nat, j:nat)
  requires i <= j+1
  ensures sum(i, j, k => if i<=k<=j then j-k+i else 0) == sum(i, j, k => k)

lemma {:axiom} lem_sumGuardedShiftLowerBound(i:int, j:int, f:int->int)
  //requires i+1 <= j
  ensures    sum(i+1, j, k => if i+1<=k<=j then f(k) else 0) 
          == sum(i+1, j, k => if i<=k<=j then f(k) else 0) 

// i <= j+1 ==>   sum_{k=i}^{j}ITE(i<=k<=j,f(k),0) 
//              = f(i) + sum_{k=i+1}^{j}ITE(i+1<=k<=j,f(k),0)
lemma {:axiom} lem_sumGuardedDropFirst(i:int, j:int, f:int->int)
  requires i <= j+1
  ensures    sum(i, j, k => if i<=k<=j then f(k) else 0) 
          ==   (if i<=i<=j then f(i) else 0) 
             + sum(i+1, j, k => if i+1<=k<=j then f(k) else 0) 

lemma lem_solveInnerSum(i:nat, N:nat, c:nat)
  requires 0 <= i <= N+1
  decreases N - i
  ensures    sum(i, N, k => sum(k, N, k' => c)) 
          == sum(i, N, k => if i<=k<=N then c*(N-k+1) else 0)
{ 
  if i == N+1 {   
    // BC: i > N
    calc {
        sum(N+1, N, k => sum(k, N, k' => c));
      == { assert N+1 > N; reveal sum(); } 
        0;
      == { assert N+1 > N; reveal sum(); } 
        sum(N+1, N, k => if N+1<=k<=N then c*(N-k+1) else 0); 
    }
  } else {  
    // Step. i <= N
    //   IH: sum(i+1, N, k => sum(k, N, k' => c)) = sum(i+1, N, k => ITE(i+1<=k<=N, c*(N-k+1), 0))
    //    T: sum(i, N, k => sum(k, N, k' => c))   = sum(i, N, k => ITE(i<=k<=N, c*(N-k+1), 0))
    calc {  
         sum(i, N, k => sum(k, N, k' => c));
      == { reveal sum(); }
         sum(i, N, k => c) + sum(i+1, N, k => sum(k, N, k' => c));
      == { lem_solveInnerSum(i+1, N, c); }  // by IH
         sum(i, N, k => c) + sum(i+1, N, k => if i+1<=k<=N then c*(N-k+1) else 0);
      == { lem_sum_constAll(i, N); } 
         c*(N-i+1) + sum(i+1, N, k => if i+1<=k<=N then c*(N-k+1) else 0);      
      == { assert i<=i; } 
         (if i<=i<=N then c*(N-i+1) else 0) + sum(i+1, N, k => if i+1<=k<=N then c*(N-k+1) else 0);      
      == { lem_solveInnerSumAUX(i, N, c); }      
         sum(i, N, k => if i<=k<=N then c*(N-k+1) else 0);           
    }
  } 
}
// lem_sumGuardedDropFirst(i, N, k => if i<=k<=N then c*(N-k+1) else 0);
//  lem_solveInnerSumAUX(i, N, c);

lemma lem_solveInnerSumAUX(i:nat, N:nat, c:nat)
  requires 0 <= i <= N
  ensures    (if i<=i<=N then c*(N-i+1) else 0) 
             + sum(i+1, N, k => if i+1<=k<=N then c*(N-k+1) else 0)
          == sum(i, N, k => if i<=k<=N then c*(N-k+1) else 0)
{ 
  calc {
       sum(i, N, k => if i<=k<=N then c*(N-k+1) else 0);
    == { reveal sum(); }
       (if i<=i<=N then c*(N-i+1) else 0) + sum(i+1, N, k => if i<=k<=N then c*(N-k+1) else 0);
    == { assert i+1 <= N+1; assert forall k :: i+1 <= k <= N ==> 
       ((k => (if i+1<=k<=N then c*(N-k+1) else 0))(k) == (k => (if i<=k<=N then c*(N-k+1) else 0))(k));
         lem_sum_leibniz(i+1, N, k => (if i+1<=k<=N then c*(N-k+1) else 0), 
                                k => (if i<=k<=N then c*(N-k+1) else 0)); }
       (if i<=i<=N then c*(N-i+1) else 0) + sum(i+1, N, k => if i+1<=k<=N then c*(N-k+1) else 0); 
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