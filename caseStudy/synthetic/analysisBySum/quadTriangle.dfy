include "../../../theory/math/LemFunction.dfy"
include "../../../theory/math/SumInt.dfy"
include "../../../theory/math/TypeR0.dfy"
include "../../../theory/Complexity.dfy"

import opened LemFunction
import opened SumInt
import opened TypeR0
import opened Complexity

type Input {
  function size() : nat
}

ghost function f(n:nat) : nat
{
  (n*(n+1))/2
}

method quadTriangle(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
  ensures tIsBigO(x.size(), t as R0, quadGrowth())
{
  var N := x.size();
  t := 0; reveal sum();

  var i, j := 0, 0;
  while i != N
    invariant 0 <= i <= N
    invariant t == sum(1, i, k => sum(k, N, k' => 1))
    decreases N - i
  {
    j := i; ghost var t' := 0;
    while j != N
      invariant i <= j <= N
      invariant t' == sum(i+1, j, k' => 1)
      decreases N - j
    {
      // Op. interesante
      lem_sum_DropLastAuto(i+1,j);
      j := j+1 ;
      t' := t'+1 ;
    }
    lem_sum_DropLastAuto(1,i);
    i := i+1 ;
    t := t+t' ;
  }

  assert t == sum(1, N, k => sum(k, N, k' => 1));
  assert t == f(N) by { lem_solveSum(1, N, 1); } 
  assert liftToR0(f) in O(quadGrowth()) by { var c, n0 := lem_fBigOquad(); }
} 

method quadTriangleFor(x:Input) returns (ghost t:nat)
  ensures t == f(x.size())
  ensures tIsBigO(x.size(), t as R0, quadGrowth())
{
  var N := x.size();
  t := 0; reveal sum();

  for i := 0 to N
    invariant t == sum(1, i, k => sum(k, N, k' => 1))
  {
    ghost var t' := 0;
    for j := i to N
      invariant t' == sum(i+1, j, k' => 1)
    {
      // Op. interesante
      lem_sum_DropLastAuto(i+1,j);
      t' := t'+1;
    }
    lem_sum_DropLastAuto(1,i);
    t := t+t';
  }
  
  assert t == sum(1, N, k => sum(k, N, k' => 1));
  assert t == f(N) by { lem_solveSum(1, N, 1); } 
  assert liftToR0(f) in O(quadGrowth()) by { var c, n0 := lem_fBigOquad(); }
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
      == ((n*(n+1))/2) as R0; 
      <= { assert (n*(n+1))/2 <= n*n; }
         (n*n) as R0;   
      <= c * (n*n) as R0;
      == c*quadGrowth()(n);
    }
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
    == { lem_sum_Leibniz(1, N, k => 1*(N-k+1),
                              k => N-k+1); }
       sum(1, N, k => (N-k+1));
    == { lem_sum_RevIndex(1, N); }
       sum(1, N, k => k); 
    == { lem_sum_Triangle(N); }  
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
      == { lem_sum_constAll(i, N); } 
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