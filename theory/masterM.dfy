
include "./complexity.dfy"

// Following recurrence models a recursive computation where
//      a = Branching factor, or number of recursive calls. Controls the breadth of computation.
//      b = Step Size. Controls the depth of computation, and determines base case size.
//      c = Work at the base case
//   w(n) = Additive term, work by recursive call.
//
//  It is assumed sub-exponential work is donde at each recursive call
//  (if not we would be doing exponential work from the very beggining!).
//
// Let T:nat->R0 be such that
//   T(n) = / c                 , n <= b        
//          \ a*T(n-b) + w(n)   , n > b           
// where a>0, b>0 and w in O(n^k) for some k.    
// Then:
//   T(n) = / O(n^{k+1})        , a = 1
//          \ O(n^k*a^{n/b})    , a > 1
//
// Note. Always match w to the tightest Θ(n^k) it belongs. 
//       - It is neccesary and sufficient to conclude the 
//         thight Θ(n^{k+1}) bound when a=1.
//       - It is neccesary, but not always sufficient, to conclude the 
//         thight Θ(n^k*a^{n/b}) bound when a>1.
//       In general, we can only be sure of O type bounds. Thigher Θ bounds
//       require a case by case analysis.
lemma masterMethodLR(a:nat, b:nat, c:R0, T:nat->R0, w:nat->R0, k:R0)  
  requires a > 0 && b > 0
  requires bigOR0(w, n => powr0(n as R0, k))
  requires forall n:nat :: T(n) == TbodyLR(a, b, c, T, w, k, n) 

  ensures a == 1 ==> bigOR0(T, (n:nat) => powr0(n as R0, k + 1.0))
  ensures a > 1  ==> bigOR0(T, (n:nat) => powr0(n as R0, k)*powr0(a as R0, (n/b) as R0))
{
  // proof using masterMethodLR2 with s := b.
  assert a > 0;   
  assert b > 0;   
  assert b >= b - 1;
  assert bigOR0(w, n => powr0(n as R0, k));
  assert forall n:nat :: T(n) == TbodyLR(a, b, c, T, w, k, n); 
  assert forall n:nat :: T(n) == TbodyLR2(a, b, c, b, T, w, k, n)
    by { reveal TbodyLR, TbodyLR2; } 

  masterMethodLR2(a, b, c, b, T, w, k);
}

opaque ghost function TbodyLR(a:nat, b:nat, c:R0, T:nat->R0, w:nat->R0, k:R0, n:nat) : R0
{   
  if   n <= b 
  then c
  else (a as R0)*T(n - b) + w(n)   
} 

// Introduce new "s" step parameter and relax b >= 0 for the base case.
// This encompass recurrences with base case n>=0.
// Well founded sufficient condition is b >= s-1.
// masterMethodLR is a special case of this with s := b.
//
// Let T:nat->R0 be such that
//   T(n) = / c                 , n <= b        
//          \ a*T(n-s) + w(n)   , n > b           
// where a>0, s>0, b >= s-1 and w in O(n^k) for some k.    
// Then:
//   T(n) = / O(n^{k+1})        , a = 1
//          \ O(n^k*a^{n/s})    , a > 1
lemma {:axiom} masterMethodLR2(a:nat, b:nat, c:R0, s:nat, T:nat->R0, w:nat->R0, k:R0)  
  requires a > 0 && s > 0 && b >= s-1
  requires bigOR0(w, n => powr0(n as R0, k)) 
  requires forall n:nat :: T(n) == TbodyLR2(a, b, c, s, T, w, k, n) 

  ensures a == 1 ==> bigOR0(T, (n:nat) => powr0(n as R0, k + 1.0))
  ensures a > 1  ==> bigOR0(T, (n:nat) => powr0(n as R0, k)*powr0(a as R0, (n/s) as R0))

opaque ghost function TbodyLR2(a:nat, b:nat, c:R0, s:nat, T:nat->R0, w:nat->R0, k:R0, n:nat) : R0
  requires b >= s-1
{   
  if   n <= b 
  then c
  else (a as R0)*T(n - s) + w(n)   
} 

//**************************************************************************//


