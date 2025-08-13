include "../../theory/math/ExpReal.dfy"
include "../../theory/math/SumReal.dfy"
include "../../theory/math/TypeR0.dfy"
include "../../theory/ComplexityR0.dfy"
include "./linearSearch.dfy"

import opened ExpReal
import opened SumReal
import opened TypeR0
import opened ComplexityR0

ghost function T<A>(s:seq<A>, x:A, i:nat) : nat
  requires 0 <= i < |s|
  requires s[i] == x
{
  i+1
}

// For the purposes of our average case analysis, the core algorithm assumes
// the target element appears in the sequence.
ghost method linearSearchAT<A>(s:seq<A>, x:A) returns (i:nat, t:nat)
  requires x in s
  ensures  post(s, x, i)
  ensures  exists k :: 0 <= k < |s| && s[k] == x && t == T(s, x, k)
{
  var n:nat;
  i, n, t := 0, |s|, 0;
  while i != n
    invariant inv(s, x, i, n)
    invariant i <= n-1 ==> t == i    // =  T(|s|) - T(|s|-i)
    invariant i == n   ==> t == i+1  // = (T(|s|) - T(|s|-i)) + 1
    decreases n - i
  {
    if s[i] != x {  // Op. interesante
      i := i + 1 ;     
    } else {
      n := i;  // break;
    }
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
  ensures  tIsBigO(N, tE, linGrowth())
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
    var _, t := linearSearchAT(s, x); 
    assert exists k :: 0 <= k < |s| && s[k] == x && t == k+1;
    assert t == T(s,x,p);
    
    // Add weighted contribution to expectation
    lem_sum_dropLastAll(0, p-1);
    tE := tE + t as real * probability(s,x,p);
    p  := p + 1;
  }
  assert tE == sum(0, N-1, i => (i+1) as real * (1.0 / N as real)); 
  assert tE == Tavg(N) by { lem_solveSum(N); }

  assert Tavg in O(linGrowth()) by { var c, n0 := lem_TavgBigOlin(); }
}

ghost method inputScenario<A>(N:nat, p:nat) returns (s0:seq<A>, x0:A)
  requires N > 0
  requires 0 <= p < N
  ensures  |s0| == N
  ensures  forall i,j :: 0 <= i <= j < |s0| && i != j ==> s0[i] != s0[j]
  ensures  s0[p] == x0
{
  assume {:axiom} 
    exists s:seq<A> :: |s| == N && (forall i,j :: 0 <= i <= j < N && i != j ==> s[i] != s[j]);
  s0 :| |s0| == N && forall i,j :: 0 <= i <= j < N && i != j ==> s0[i] != s0[j];
  assume {:axiom} 
    exists x:A :: s0[p] == x;
  x0 :| s0[p] == x0;
}

ghost function probability<A>(s:seq<A>, x:A, p:nat) : R0
  requires 0 <= p < |s|
  requires s[p] == x
  requires forall i :: 0 <= i < |s| && i != p ==> s[i] != s[p]
{
  1.0 / |s| as R0
}

lemma lem_solveSum(N:nat)
  requires N > 0
  ensures  Tavg(N) == sum(0, N-1, i => (i+1) as real * (1.0 / N as real))
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
  ensures bigOfrom(c, n0, Tavg, linGrowth())
{
  // we show that c=1 and n0=1
  c, n0 := 1.0, 1;
  forall n:nat | 0 <= n0 <= n
    ensures Tavg(n) <= c*linGrowth()(n)
  {
    calc {
         Tavg(n);
      == (n + 1) as real / 2.0;
      <= n as real;
      == { lem_expOne(n as R0); }
         exp(n as R0, 1.0);
    }
  }
}