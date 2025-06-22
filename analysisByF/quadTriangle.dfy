
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
  var i, j;
  i, j, t, t' := 0, 0, 0, 0;
  while i != N
    invariant 0 <= i <= N
    invariant t == T1(N,0) - T1(N,i) // = T1(N, N-i)
    decreases N - i
  {
    j := i; t' := 0; 
    while j != N
      invariant i <= j <= N && i != N
      invariant t' == T2(N,i) - T2(N,j)  // = T2(N, (N-j)+i)
      decreases N - j
    {
      // Op. interesante
      j  := j+1;
      t' := t'+1;
    }
    lem_T2reverseIndex(N, i); 
    i := i+1;
    t := t+t';
  }
  assert t == T1(N, 0); 
  assert t == f(N) by { lem_T1closed(N, 0); }
  assert t <= f(N); 
 
  assert bigO(f, quadGrowth()) by { var c, n0 := lem_fBigOquad(); }  
} 

ghost function T1(N:nat, i:int): nat
  requires  0 <= i <= N
  decreases N - i
{
  if i != N 
  then T1(N, i+1) + T2(N, i)
  else 0
}

ghost function T2(N:nat, j:int): nat
  requires  0 <= j <= N
  decreases N - j
{
  if j != N 
  then T2(N, j+1) + 1 
  else 0
}

lemma lem_T2closed(N:nat, j:int)
  requires 0 <= j <= N
  decreases N - j
  ensures T2(N, j) == N - j
{
  if j != N  {
    lem_T2closed(N, j+1);
  }
}

lemma {:axiom} lem_T2reverseIndex(N:nat, i:int)
  requires 0 <= i < N
  ensures T2(N, i) == T2(N, N-(i+1))
// Esto es esencialmente lem_sum_revIndex
// pero en forma de recurrencia

lemma lem_T1closed(N:nat, i:nat)
  requires 0 <= i <= N
  decreases N - i
  ensures T1(N, i) == ((N-i)*((N-i)+1))/2
{ 
  if i != N {
    lem_T2closed(N, i);
    lem_T1closed(N, i+1);
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
      ==
        (n*(n+1))/2; 
      <=
        n*n;   
    }
    assert n >= n0 ==> f(n) <= c*quadGrowth()(n) 
      by { reveal pow(); } 
  }
}

//**************************************************************************//

ghost method testT2() {
  var N := 4; 
  var i := 0; 
  var r := T2(N, i);
  assert r == 4; 
  assert N - i == 4;

  i := 1; 
  r := T2(N, i);
  assert r == 3;
  assert N - i == 3;

  i := 2; 
  r := T2(N, i);
  assert r == 2;
  assert N - i == 2;  

  i := 3; 
  r := T2(N, i);
  assert r == 1;
  assert N - i == 1; 

  i := 4; 
  r := T2(N, i);
  assert r == 0;
  assert N - i == 0;    
}  

ghost method testT1() {
  var N:nat := 0;
  var r := T1(N, 0);
  assert r == 0; 
  assert (N*(N+1))/2 == 0; 

  N := 1;
  r := T1(N, 0);
  assert r == 1;
  assert (N*(N+1))/2 == 1;

  N := 2;
  r := T1(N, 0); 
  assert r == 3;
  assert (N*(N+1))/2 == 3;

  N := 3;
  r := T1(N, 0); 
  assert r == 6;
  assert (N*(N+1))/2 == 6;

  N := 4;
  r := T1(N, 0); 
  assert r == 10;
  assert (N*(N+1))/2 == 10;
}