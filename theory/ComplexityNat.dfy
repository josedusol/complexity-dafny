include "./math/FloorCeil.dfy"
include "./math/ExpNat.dfy"
include "./math/LemFunction.dfy"
include "./math/Misc.dfy"
include "./math/TypeR0.dfy"
include "./ComplexityR0.dfy"

/**************************************************************************
  Complexity definitions for non-negative integer functions
**************************************************************************/

module ComplexityNat { 
  import opened ComplexityR0
  import opened ExpNat
  import opened FloorCeil   
  import opened Misc 
  import opened LemFunction
  import opened TypeR0 

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
  // Each result is proved in the lifted domain nat->R0
  // and then casted back to nat->nat 

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

}