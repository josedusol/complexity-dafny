
include "../theory/complexity.dfy"

ghost function f(N:nat) : nat
{
  pow(N,2)
}

method quadCall(N:nat)
  returns (ghost t:nat)
  ensures t == f(N)
  ensures tIsBigO(N, t, quadGrowth())
{
  var i;
  i, t := 0, 0;
  while i != N
    invariant 0 <= i <= N
    invariant t == T1(N,0) - T1(N,i)  // = T1(N, N-i)
    decreases N - i
  {
    var t' := quadCallSub(N);
    lem_T1closed(N, N-i); lem_T1closed(N, N-(i+1));
    i := i+1;
    t := t + t'; 
  }
  assert t == T1(N, 0); 
  assert t == f(N) by { reveal pow(); lem_T1closed(N, 0); }
  assert t <= f(N); 
 
  assert bigO(f, quadGrowth()) by { var c, n0 := lem_fBigOquad(); }
} 

ghost function f'(N:nat) : nat
{
  N
}

method quadCallSub(N:nat)
  returns (ghost t:nat)
  ensures t == f'(N)
  ensures tIsBigO(N, t, linGrowth())
{
  var i;
  i, t := 0, 0;
  while i != N
    invariant 0 <= i <= N
    invariant t == T2(N,0) - T2(N,i)  // = T1(N, N-i)
    decreases N - i
  {
    // Op. interesante
    i := i+1;
    t := t+1;
  }
  assert t == T2(N, 0); 
  assert t == f'(N) by { lem_T2closed(N, 0); }
  assert t <= f'(N); 
 
  assert bigO(f', linGrowth()) by { var c, n0 := lem_subBigOlin(); }
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

lemma lem_subBigOlin() returns (c:nat, n0:nat)
  ensures bigOfrom(c, n0, f', linGrowth())
{
  // we show that c=1 and n0=0
  c, n0 := 1, 0;
  forall n:nat | 0 <= n0 <= n
    ensures f'(n) <= c*linGrowth()(n)
  {
    calc {
         f'(n);
      == n;
      == { reveal pow(); }
         pow(n,1);
    }
    assert f'(n) <= c*linGrowth()(n); 
  }
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
      == pow(n,2);
      == { reveal pow(); }
         n*n;   
    }
    assert f(n) <= c*quadGrowth()(n); 
  }
}