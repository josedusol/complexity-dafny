
include "./math.dfy"
include "./bounds.dfy"

/**************************************************************************
  Complexity definitions for non-negative integer functions 
**************************************************************************/
 
ghost predicate bigO(f:nat->nat, g:nat->nat)
{ 
  exists c:nat, n0:nat :: bigOfrom(c, n0, f, g) 
}

ghost predicate bigOfrom(c:nat, n0:nat, f:nat->nat, g:nat->nat)
{
  forall n:nat :: 0 <= n0 <= n ==> f(n) <= c*g(n)  
}

ghost predicate tIsBigO(n:nat, t:nat, g:nat->nat)
{ 
  exists f:nat->nat :: t <= f(n) && bigO(f,g)
}

ghost predicate isPoly(f:nat->nat)
{ 
  exists k:nat :: bigO(f, n => pow(n,k))
}
 
/**************************************************************************
  Complexity definitions lifted for functions nat->R0
**************************************************************************/
 
ghost predicate bigOR0(f:nat->R0, g:nat->R0)
{ 
  exists c:R0, n0:nat :: bigOR0from(c, n0, f, g) 
}

ghost predicate bigOR0from(c:R0, n0:nat, f:nat->R0, g:nat->R0)
{
  forall n:nat :: 0 <= n0 <= n ==> f(n) <= c*g(n)
}
 
/**************************************************************************
  Mapping of results between unlifted and lifted functions
**************************************************************************/

// If we prove f ∈ O(g) for f,g:nat->nat then we can extend
// the result for the lifted versions f',g':nat->R0.
lemma lem_bigOtoBigOR0(f:nat->nat, g:nat->nat)  
  requires bigO(f, g) 
  ensures  bigOR0(liftToR0(f), liftToR0(g))
{    
  var c:nat, n0:nat :| bigOfrom(c, n0, f, g);  
  assert forall n:nat :: 0 <= n0 <= n ==> f(n) <= c*g(n);

  assert forall n:nat :: liftToR0(f)(n) == f(n) as R0;
  assert forall n:nat :: liftToR0(g)(n) == g(n) as R0;

  var c':R0 := c as R0; // just view c:nat as a R0 number
  assert forall n:nat :: 0 <= n0 <= n ==> liftToR0(f)(n) <= c'*liftToR0(g)(n); 
  assert bigOR0from(c', n0, liftToR0(f), liftToR0(g));
}
 
// If we prove f' ∈ O(g') for the lifted versions of f,g:nat->nat
// then we can get back the result
lemma lem_bigOR0toBigO(f:nat->nat, g:nat->nat)  
  requires bigOR0(liftToR0(f), liftToR0(g))
  ensures  bigO(f, g)
{ 
  var c:R0, n0:nat :| bigOR0from(c, n0, liftToR0(f), liftToR0(g));
  assert forall n:nat :: 0 <= n0 <= n ==> liftToR0(f)(n) <= c*liftToR0(g)(n);
  
  assert forall n:nat :: liftToR0(f)(n) == f(n) as R0;
  assert forall n:nat :: liftToR0(g)(n) == g(n) as R0;

  var c':nat := ceil(c);  // c may be non-integer, so we bound with it's ceil
  assert c <= c' as R0;
  assert forall n:nat :: c*liftToR0(g)(n) <= (c' as R0)*liftToR0(g)(n);
  assert forall n:nat :: 0 <= n0 <= n ==> f(n) <= c'*g(n); 
  assert bigOfrom(c', n0, f, g);
}

/**************************************************************************
  Basic O properties
**************************************************************************/

// Reflexivity
// f ∈ O(f)
lemma lem_bigOR0_refl(f:nat->R0)  
  ensures bigOR0(f, f) 
{  
  // we show that c=1.0 and n0=0
  assert forall n:nat :: 0 <= 0 <= n ==> f(n) <= 1.0*f(n);
  assert bigOR0from(1.0, 0, f, f);
}

// If f ∈ O(g) and a>0 then a*f ∈ O(g)
lemma lem_bigOR0_constFactor(f:nat->R0, g:nat->R0, a:R0)  
  requires bigOR0(f, g) 
  requires a > 0.0 
  ensures  bigOR0(n => a*f(n), g) 
{  
  var c:R0, n0:nat :| bigOR0from(c, n0, f, g);  
  assert forall n:nat :: 0 <= n0 <= n ==> f(n) <= c*g(n);
  
  // we show that c'=a*c and n0'=n0
  assert forall n:nat :: 0 <= n0 <= n ==> a*f(n) <= (a*c)*g(n);
  assert bigOR0from(a*c, n0, n => a*f(n), g);
}

// If f1 ∈ O(g1) and f2 ∈ O(g2) then f1+f2 ∈ O(g1+g2)
lemma lem_bigOR0_sum(f1:nat->R0, g1:nat->R0, f2:nat->R0, g2:nat->R0)  
  requires bigOR0(f1, g1) 
  requires bigOR0(f2, g2) 
  ensures  bigOR0(n => f1(n)+f2(n), n => g1(n)+g2(n)) 
{  
  var c1:R0, n1:nat :| bigOR0from(c1, n1, f1, g1);  
  assert forall n:nat :: 0 <= n1 <= n ==> f1(n) <= c1*g1(n);
  var c2:R0, n2:nat :| bigOR0from(c2, n2, f2, g2);  
  assert forall n:nat :: 0 <= n2 <= n ==> f2(n) <= c2*g2(n);   
  
  // we show that c=c1+c2 and n0=n1+n2
  assert forall n:nat :: 0 <= n1+n2 <= n ==> f1(n) + f2(n) <= c1*g1(n) + c2*g2(n);
  assert forall n:nat :: 0 <= n1+n2 <= n ==> f1(n) + f2(n) <= (c1+c2)*(g1(n) + g2(n));
  assert bigOR0from(c1+c2, n1+n2, n => f1(n)+f2(n), n => g1(n)+g2(n));
}

// If f1 ∈ O(g1) and f2 ∈ O(g2) then f1*f2 ∈ O(g1*g2)
lemma lem_bigOR0_prod(f1:nat->R0, g1:nat->R0, f2:nat->R0, g2:nat->R0)  
  requires bigOR0(f1, g1) 
  requires bigOR0(f2, g2) 
  ensures  bigOR0(n => f1(n)*f2(n), n => g1(n)*g2(n)) 
{  
  var c1:R0, n1:nat :| bigOR0from(c1, n1, f1, g1);  
  assert forall n:nat :: 0 <= n1 <= n ==> f1(n) <= c1*g1(n);
  var c2:R0, n2:nat :| bigOR0from(c2, n2, f2, g2);  
  assert forall n:nat :: 0 <= n2 <= n ==> f2(n) <= c2*g2(n);   
  
  // we show that c=c1*c2 and n0=n1+n2
  assert forall n:nat :: 0 <= n1+n2 <= n ==> f1(n)*f2(n) <= (c1*g1(n))*(c2*g2(n));
  assert forall n:nat :: 0 <= n1+n2 <= n ==> f1(n)*f2(n) <= (c1*c2)*(g1(n)*g2(n));
  assert bigOR0from(c1*c2, n1+n2, n => f1(n)*f2(n), n => g1(n)*g2(n));
}

// Transitivity
// If f ∈ O(g) and g ∈ O(h) then f ∈ O(h)
lemma lem_bigOR0_trans(f:nat->R0, g:nat->R0, h:nat->R0)  
  requires bigOR0(f, g) 
  requires bigOR0(g, h) 
  ensures  bigOR0(f, h) 
{  
  var c1:R0, n1:nat :| bigOR0from(c1, n1, f, g);  
  assert forall n:nat :: 0 <= n1 <= n ==> f(n) <= c1*g(n);
  var c2:R0, n2:nat :| bigOR0from(c2, n2, g, h);  
  assert forall n:nat :: 0 <= n2 <= n ==> g(n) <= c2*h(n);   
  
  // we show that c=c1*c2 and n0=n1+n2
  forall n:nat | 0 <= n1+n2 <= n
    ensures f(n) <= c1*c2*h(n)
  {
    if 0 <= n1+n2 <= n {
      calc {
          f(n); 
        <=
          c1*g(n);
        <= { assert g(n) <= c2*h(n); } 
          c1*c2*h(n);         
      }
    }
  }
  assert bigOR0from(c1*c2, n1+n2, f, h);
}

// TODO:  If f ∈ O(g) then f+g ∈ O(g)

//**************************************************************************//

// The same properties as before but for unlifted functions 
// Each result is proved in the lifted domain nat->R0
// using earlier proofs and then casted back to nat->nat 

// Reflexivity
// f ∈ O(f)
lemma lem_bigO_refl(f:nat->nat)  
  ensures bigO(f, f) 
{  
  var f':nat->R0 := liftToR0(f);
  assert bigOR0(f', f')
    by { lem_bigOR0_refl(f'); }
  lem_bigOR0toBigO(f, f);
}

// If f ∈ O(g) and a>0 then a*f ∈ O(g)
lemma lem_bigO_constFactor(f:nat->nat, g:nat->nat, a:nat)  
  requires bigO(f, g) 
  requires a > 0
  ensures  bigO(n => a*f(n), g) 
{  
  var f':nat->R0 := liftToR0(f);
  var g':nat->R0 := liftToR0(g); 
  var a':R0 := a as R0; 
  assert bigOR0(f', g') 
    by { lem_bigOtoBigOR0(f, g); }
  assert bigOR0(n => a'*f'(n), g')  
    by { lem_bigOR0_constFactor(f', g', a'); }
  lem_bigOR0toBigO(n => a*f(n), g)
    by { lem_funExt(liftToR0(n => a*f(n)), n => a'*f'(n)); }
} 

// If f1 ∈ O(g1) and f2 ∈ O(g2) then f1+f2 ∈ O(g1+g2)
lemma lem_bigO_sum(f1:nat->nat, g1:nat->nat, f2:nat->nat, g2:nat->nat)  
  requires bigO(f1, g1) 
  requires bigO(f2, g2) 
  ensures  bigO(n => f1(n)+f2(n), n => g1(n)+g2(n)) 
{  
  var f1':nat->R0 := liftToR0(f1);
  var f2':nat->R0 := liftToR0(f2);
  var g1':nat->R0 := liftToR0(g1); 
  var g2':nat->R0 := liftToR0(g2); 
  assert bigOR0(f1', g1') 
    by { lem_bigOtoBigOR0(f1, g1); }
  assert bigOR0(f2', g2') 
    by { lem_bigOtoBigOR0(f2, g2); } 
  assert bigOR0(n => f1'(n)+f2'(n), n => g1'(n)+g2'(n))  
    by { lem_bigOR0_sum(f1', g1', f2', g2'); }
  lem_funExt(liftToR0(n => f1(n)+f2(n)), n => f1'(n)+f2'(n));
  lem_funExt(liftToR0(n => g1(n)+g2(n)), n => g1'(n)+g2'(n));  
  lem_bigOR0toBigO(n => f1(n)+f2(n), n => g1(n)+g2(n));     
}

// If f1 ∈ O(g1) and f2 ∈ O(g2) then f1*f2 ∈ O(g1*g2)
lemma lem_bigO_prod(f1:nat->nat, g1:nat->nat, f2:nat->nat, g2:nat->nat)  
  requires bigO(f1, g1) 
  requires bigO(f2, g2) 
  ensures  bigO(n => f1(n)*f2(n), n => g1(n)*g2(n))  
{  
  var f1':nat->R0 := liftToR0(f1);
  var f2':nat->R0 := liftToR0(f2);
  var g1':nat->R0 := liftToR0(g1); 
  var g2':nat->R0 := liftToR0(g2);  
  assert A: bigOR0(f1', g1') 
    by { lem_bigOtoBigOR0(f1, g1); }
  assert B: bigOR0(f2', g2') 
    by { lem_bigOtoBigOR0(f2, g2); } 
  assert bigOR0(n => f1'(n)*f2'(n), n => g1'(n)*g2'(n))  
    by { reveal A, B; lem_bigOR0_prod(f1', g1', f2', g2'); }
  lem_funExt(liftToR0(n => f1(n)*f2(n)), n => f1'(n)*f2'(n));
  lem_funExt(liftToR0(n => g1(n)*g2(n)), n => g1'(n)*g2'(n));
  lem_bigOR0toBigO(n => f1(n)*f2(n), n => g1(n)*g2(n));
}   

// Transitivity
// If f ∈ O(g) and g ∈ O(h) then f ∈ O(h)
lemma lem_bigO_trans(f:nat->nat, g:nat->nat, h:nat->nat)  
  requires bigO(f, g)
  requires bigO(g, h)
  ensures  bigO(f, h) 
{  
  var f':nat->R0 := liftToR0(f);
  var g':nat->R0 := liftToR0(g);  
  var h':nat->R0 := liftToR0(h);  
  assert bigOR0(f', g') 
    by { lem_bigOtoBigOR0(f, g); }
  assert bigOR0(g', h') 
    by { lem_bigOtoBigOR0(g, h); }
  assert bigOR0(f', h')  
    by { lem_bigOR0_trans(f', g', h'); }
  lem_bigOR0toBigO(f, h);
}

/**************************************************************************
  Functions for common growth rates
**************************************************************************/

ghost function constGrowth() : nat->nat
{   
  n => 1
}

ghost function logGrowth() : nat->nat
{   
  n => if n>0 then log2(n) else 0
}

ghost function logGrowth2() : nat->nat
{   
  n => log2(n+1)
}

ghost function sqrtGrowth() : nat->nat
{   
  n => sqrt(n)
}

ghost function linGrowth() : nat->nat
{   
  n => pow(n,1)
}

ghost function quadGrowth() : nat->nat
{   
  n => pow(n,2)
}

ghost function cubicGrowth() : nat->nat
{   
  n => pow(n,3)
}

ghost function polyGrowth(k:nat) : nat->nat
{   
  n => pow(n,k)
}

ghost function polyGrowthR0(k:R0) : nat->R0
{   
  n => powr(n as R0,k)
}

ghost function expGrowth() : nat->nat
{   
  n => pow(2,n)
}

ghost function facGrowth() : nat->nat
{   
  n => fac(n)
}

ghost function dexpGrowth() : nat->nat
{   
  n => pow(2,pow(2,n))
}

/**************************************************************************
  Growth comparision
**************************************************************************/

// log2(n) ∈ O(n) 
lemma lem_bigO_logBigOlin()
  ensures bigO(logGrowth(), linGrowth()) 
{ 
  // we show that c=1 and n0=1
  forall n:nat | 0 <= 1 <= n
    ensures logGrowth()(n) <= 1*linGrowth()(n)
  {
    if 0 <= 1 <= n {
      reveal pow();
      lem_log2nLEQnMinus1(n);
      assert logGrowth()(n) <= 1*linGrowth()(n);
    }
  }
  assert bigOfrom(1, 1, logGrowth(), linGrowth());
}

// log2(n+1) ∈ O(n) 
lemma lem_bigO_logBigOlinV2()
  ensures bigO(logGrowth2(), linGrowth()) 
{ 
  // we show that c=1 and n0=1
  forall n:nat | 0 <= 1 <= n
    ensures logGrowth2()(n) <= 1*linGrowth()(n)
  {
    if 0 <= 1 <= n {
      reveal pow();
      lem_log2nPlus1LEQn(n);
      assert logGrowth2()(n) <= 1*linGrowth()(n);
    }
  }
  assert bigOfrom(1, 1, logGrowth2(), linGrowth());
}

// n ∈ O(n^2) 
lemma lem_bigO_linBigOquad()
  ensures bigO(linGrowth(), quadGrowth()) 
{ 
  // we show that c=1 and n0=0
  forall n:nat | 0 <= 0 <= n
    ensures linGrowth()(n) <= 1*quadGrowth()(n)
  {
    if 0 <= 0 <= n {
      reveal pow();
      lem_nLQpown2(n);
      assert linGrowth()(n) <= 1*quadGrowth()(n);
    }
  }
  assert bigOfrom(1, 0, linGrowth(), quadGrowth());
}

// n^2 ∈ O(2^n)  
lemma lem_bigO_quadBigOexp()
  ensures bigO(quadGrowth(), expGrowth()) 
{ 
  // we show that c=1 and n0=4
  forall n:nat | 0 <= 4 <= n
    ensures quadGrowth()(n) <= 1*expGrowth()(n)
  {
    if 0 <= 4 <= n {
      reveal pow();
      lem_pown2LQpow2n(n);
      assert quadGrowth()(n) <= 1*expGrowth()(n);
    }
  }
  assert bigOfrom(1, 4, quadGrowth(), expGrowth());
}

// n ∈ O(2^n)  
// Follows from transitivity of n ∈ O(n^2) and n^2 ∈ O(2^n)  
lemma lem_bigO_linBigOexp()
  ensures bigO(linGrowth(), expGrowth()) 
{ 
  assert bigO(linGrowth(), quadGrowth()) by { lem_bigO_linBigOquad(); }
  assert bigO(quadGrowth(), expGrowth()) by { lem_bigO_quadBigOexp(); }
  lem_bigO_trans(linGrowth(), quadGrowth(), expGrowth());
}