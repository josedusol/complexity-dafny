include "../theory/math/SumReal.dfy"
include "../theory/math/TypeR0.dfy"
include "../theory/ComplexityR0.dfy"

import opened SumReal
import opened TypeR0
import opened ComplexityR0

ghost predicate inv<A>(s:seq<A>, x:A, i:nat, n:nat)
{
     0 <= i <= n && n <= |s|
  && (0 <= n < |s| ==> s[i] == x)      
  && (n == |s|     ==> (forall j :: 0 <= j < i ==> s[j] != x))
}

ghost predicate post<A>(s:seq<A>, x:A, i:nat)
{
     (0 <= i < |s| ==> s[i] == x)
  && (i == |s|     ==> (forall j :: 0 <= j < |s| ==> s[j] != x))
}

ghost function T<A>(s:seq<A>, x:A, i:nat) : nat
  requires 0 <= i < |s|
  requires s[i] == x
{
  i+1
}

// For the purposes of our average case analysis, the core algorithm assumes
// the target element appears in the sequence.
ghost method linearSearch<A>(s:seq<A>, x:A) returns (i:nat, t:nat)
  requires x in s
  ensures  post(s, x, i)
  ensures  exists k :: 0 <= k < |s| && s[k] == x && t == T(s, x, k)
{
  var n:nat;
  i, n, t := 0, |s|, 1;
  while i != n && s[i] != x
    invariant inv(s, x, i, n)
    invariant forall j :: 0 <= j < i ==> s[j] != x
    invariant exists k :: i <= k < |s| && s[k] == x
    invariant t == i+1
    decreases n - i
  {
    i := i + 1;
    t := t + 1;
  }
  assert s[i] == x && t == T(s,x,i);
} 

ghost function Tavg(N:nat) : R0
{
  (N + 1) as real / 2.0
}

ghost method expectationLoop<A>(N:nat)
  returns (tE:real)
  requires N > 0
  ensures  tE == Tavg(N)
  ensures  tIsBigO(N, tE, n => n as R0)
{
  tE := 0.0; 
  var p := 0; reveal sum();  
  while p < N
    invariant 0 <= p <= N
    invariant tE == sum(0, p-1, i => (i+1) as real * (1.0 / N as real))
    decreases N - p
  {
    // Run algorithm in scenario where s[p] == x
    var s:seq<A>, x:A := inputScenario(N, p); 
    var _, t := linearSearch(s, x); 
    assert exists k :: 0 <= k < |s| && s[k] == x && t == k+1;
    assert t == T(s,x,p);
    
    // Add weighted contribution to expectation
    lem_sum_dropLastAll(0, p-1);
    tE := tE + t as real * probability(s,x,p);
    p  := p + 1;
  }
  assert tE == sum(0, N-1, i => (i+1) as real * (1.0 / N as real)); 
  assert tE == Tavg(N) by { lem_solveSum(N); }

  assert bigO(Tavg, n => n as R0) by { var c, n0 := lem_TavgBigOlin(); }
}

ghost function probability<A>(s:seq<A>, x:A, p:nat) : R0
  requires 0 <= p < |s|
  requires s[p] == x
  requires forall i :: 0 <= i < |s| && i != p ==> s[i] != s[p]
{
  1.0 / |s| as R0
}

ghost method inputScenario<A>(N:nat, p:nat) returns (s0:seq<A>, x0:A)
  requires N > 0
  requires 0 <= p < N
  ensures  |s0| == N
  ensures  s0[p] == x0
  ensures  forall i :: 0 <= i < |s0| && i != p ==> s0[i] != s0[p]
{
  assume {:axiom} 
    exists s:seq<A> :: |s| == N && (forall i :: 0 <= i < N && i != p ==> s[i] != s[p]);
  s0 :| |s0| == N && forall i :: 0 <= i < N && i != p ==> s0[i] != s0[p];
  assume {:axiom} 
    exists x:A :: s0[p] == x;
  x0 :| s0[p] == x0;
}

lemma lem_solveSum(N:nat)
  requires N > 0
  ensures Tavg(N) == sum(0, N-1, i => (i+1) as real * (1.0 / N as real))
{ 
  var c:real := 1.0 / N as real; 
  calc {
       sum(0, N-1, i => (i+1) as real * c);
    == { assert forall k:int :: 0<=k<=N-1 ==>   
           (i => (i+1) as real * c)(k) == (l => c*(i => (i+1) as real)(l))(k);
         lem_sum_leibniz(0, N-1, i => (i+1) as real * c, 
                                 l => c*(i => (i+1) as real)(l)); }
       sum(0, N-1, l => c*(i => (i+1) as real)(l));
    == { lem_sum_linearityConst(0, N-1, c, i => (i+1) as real); }
       c * sum(0, N-1, i => (i+1) as real);
    == { lem_sum_shiftIndex(0, N-1, 1, i => (i+1) as real); }
       c * sum(1, N, i => (i => (i+1) as real)(i-1));
    == { assert forall k:int :: 1<=k<=N ==> (i => ((i-1)+1) as real)(k) == (i => i as real)(k);
         lem_sum_leibniz(1, N, i => (i => (i+1) as real)(i-1), i => i as real); }
       c * sum(1, N, i => i as real);
    == { lem_sum_interval(1, N); }
       c * ((N*(N+1) + 1*(1-1)) as real / 2.0);
    == c * ((N*(N+1)) as real / 2.0);  
    == (1.0 / N as real) * ((N*(N+1)) as real / 2.0); 
    == (N + 1) as real / 2.0;
  }
} 

lemma lem_TavgBigOlin() returns (c:R0, n0:nat)
  ensures bigOfrom(c, n0, Tavg, n => n as R0)
{
  // we show that c=1 and n0=1
  c, n0 := 1.0, 1;
  forall n:nat | 0 <= n0 <= n
    ensures Tavg(n) <= c*(n => n as R0)(n)
  {
    calc {
         Tavg(n);
      == (n + 1) as real / 2.0;
      <= n as real;
    }
    assert Tavg(n) <= c*(n => n as R0)(n); 
  }
}