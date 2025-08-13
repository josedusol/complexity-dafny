include "./math/FloorCeil.dfy"
include "./math/LemFunction.dfy"
include "./math/TypeR0.dfy"
include "./ComplexityNat.dfy"
include "./ComplexityR0.dfy"

/******************************************************************************
  Lemmas about complexity definitions
******************************************************************************/

module LemComplexity { 
  import opened FloorCeil
  import opened LemFunction
  import opened TypeR0
  import opened ComplexityNat
  import CR0 = ComplexityR0

  /******************************************************************************
    Mapping of Big O asymptotic results between unlifted and lifted functions
  ******************************************************************************/

  // If we prove f ∈ O(g) for f,g:nat->nat then we can extend
  // the result for the lifted versions f',g':nat->R0.
  lemma lem_bigOtoBigOR0(f:nat->nat, g:nat->nat)  
    requires bigO(f, g) 
    ensures  CR0.bigO(liftToR0(f), liftToR0(g))
  {    
    var c:nat, n0:nat :| bigOfrom(c, n0, f, g);  
    assert forall n:nat :: 0 <= n0 <= n ==> f(n) <= c*g(n);

    assert forall n:nat :: liftToR0(f)(n) == f(n) as R0;
    assert forall n:nat :: liftToR0(g)(n) == g(n) as R0;

    var c':R0 := c as R0;  // just view c:nat as a R0 number
    assert forall n:nat :: 0 <= n0 <= n ==> liftToR0(f)(n) <= c'*liftToR0(g)(n); 
    assert CR0.bigOfrom(c', n0, liftToR0(f), liftToR0(g));
  }
  
  // If we prove f' ∈ O(g') for the lifted versions of f,g:nat->nat
  // then we can get back the result
  lemma lem_bigOR0toBigO(f:nat->nat, g:nat->nat)  
    requires CR0.bigO(liftToR0(f), liftToR0(g))
    ensures  bigO(f, g)
  { 
    var c:R0, n0:nat :| CR0.bigOfrom(c, n0, liftToR0(f), liftToR0(g));
    assert forall n:nat :: 0 <= n0 <= n ==> liftToR0(f)(n) <= c*liftToR0(g)(n);
    
    assert forall n:nat :: liftToR0(f)(n) == f(n) as R0;
    assert forall n:nat :: liftToR0(g)(n) == g(n) as R0;

    var c':nat := ceil(c);  // c may be non-integer, so we bound above with it's ceil
    assert c <= c' as R0;
    assert forall n:nat :: c*liftToR0(g)(n) <= (c' as R0)*liftToR0(g)(n);
    assert forall n:nat :: 0 <= n0 <= n ==> f(n) <= c'*g(n); 
    assert bigOfrom(c', n0, f, g);
  }

  /******************************************************************************
    Mapping of Big Ω asymptotic results between unlifted and lifted functions
  ******************************************************************************/

  lemma lem_bigOmToBigOmR0(f:nat->nat, g:nat->nat)  
    requires bigOm(f, g) 
    ensures  CR0.bigOm(liftToR0(f), liftToR0(g))
  {    
    var c:nat, n0:nat :| bigOmFrom(c, n0, f, g);  
    assert forall n:nat :: 0 <= n0 <= n ==> c*g(n) <= f(n);

    assert forall n:nat :: liftToR0(f)(n) == f(n) as R0;
    assert forall n:nat :: liftToR0(g)(n) == g(n) as R0;

    var c':R0 := c as R0;  // just view c:nat as a R0 number
    assert forall n:nat :: 0 <= n0 <= n ==> c'*liftToR0(g)(n) <= liftToR0(f)(n); 
    assert CR0.bigOmFrom(c', n0, liftToR0(f), liftToR0(g));
  }

  lemma lem_bigOmR0toBigOm(f:nat->nat, g:nat->nat)  
    requires CR0.bigOm(liftToR0(f), liftToR0(g))
    ensures  bigOm(f, g)
  { 
    var c:R0, n0:nat :| CR0.bigOmFrom(c, n0, liftToR0(f), liftToR0(g));
    assert forall n:nat :: 0 <= n0 <= n ==> c*liftToR0(g)(n) <= liftToR0(f)(n);
    
    assert forall n:nat :: liftToR0(f)(n) == f(n) as R0;
    assert forall n:nat :: liftToR0(g)(n) == g(n) as R0;

    var c':nat := floor(c);  // c may be non-integer, so we bound below with it's floor
    assert c' as R0 <= c;
    assert forall n:nat :: (c' as R0)*liftToR0(g)(n) <= c*liftToR0(g)(n);
    assert forall n:nat :: 0 <= n0 <= n ==> c'*g(n) <= f(n); 
    assert bigOmFrom(c', n0, f, g);
  }  

  /******************************************************************************
    Mapping of Big Θ asymptotic results between unlifted and lifted functions
  ******************************************************************************/

  lemma lem_bigThtoBigThR0(f:nat->nat, g:nat->nat)  
    requires bigTh(f, g) 
    ensures  CR0.bigTh(liftToR0(f), liftToR0(g)) 
  {
    assert bigOm(f, g) && bigO(f, g);
    lem_bigOmToBigOmR0(f, g); 
    lem_bigOtoBigOR0(f, g); 
  }
  
  lemma lem_bigThR0toBigTh(f:nat->nat, g:nat->nat)  
    requires CR0.bigTh(liftToR0(f), liftToR0(g))
    ensures  bigTh(f, g)
  {
    assert CR0.bigOm(liftToR0(f), liftToR0(g)) && CR0.bigO(liftToR0(f), liftToR0(g));
    lem_bigOmR0toBigOm(f, g);
    lem_bigOR0toBigO(f, g);
  }

  lemma lem_bigTh2toBigTh2R0(f:nat->nat, g:nat->nat)  
    requires bigTh2(f, g) 
    ensures  CR0.bigTh2(liftToR0(f), liftToR0(g))
  {
    var c1:nat, c2:nat, n0:nat :| bigThFrom(c1, c2, n0, f, g);  
    assert forall n:nat :: 0 <= n0 <= n ==> c1*g(n)  <= f(n) <= c2*g(n);

    assert forall n:nat :: liftToR0(f)(n) == f(n) as R0;
    assert forall n:nat :: liftToR0(g)(n) == g(n) as R0;

    var c1':R0 := c1 as R0;  // just view c1,c2:nat as R0 numbers
    var c2':R0 := c2 as R0;  
    assert forall n:nat :: 0 <= n0 <= n ==> c1'*liftToR0(g)(n) <= liftToR0(f)(n) <= c2'*liftToR0(g)(n); 
    assert CR0.bigThFrom(c1', c2', n0, liftToR0(f), liftToR0(g));
  } 
  
  lemma lem_bigTh2R0toBigTh2(f:nat->nat, g:nat->nat)  
    requires CR0.bigTh2(liftToR0(f), liftToR0(g))
    ensures  bigTh2(f, g)  
  {
    var c1:R0, c2:R0, n0:nat :| CR0.bigThFrom(c1, c2, n0, liftToR0(f), liftToR0(g));
    assert forall n:nat :: 0 <= n0 <= n ==> c1*liftToR0(g)(n) <= liftToR0(f)(n) <= c2*liftToR0(g)(n);
    
    assert forall n:nat :: liftToR0(f)(n) == f(n) as R0;
    assert forall n:nat :: liftToR0(g)(n) == g(n) as R0;

    var c1':nat := floor(c1);  // c1 may be non-integer, so we bound below with it's floor
    assert c1' as R0 <= c1;
    var c2':nat := ceil(c2);   // c2 may be non-integer, so we bound above with it's ceil
    assert c2 <= c2' as R0;
    assert forall n:nat :: (c1' as R0)*liftToR0(g)(n) <= c1*liftToR0(g)(n);
    assert forall n:nat :: c2*liftToR0(g)(n) <= (c2' as R0)*liftToR0(g)(n);
    assert forall n:nat :: 0 <= n0 <= n ==> c1'*g(n) <= f(n) <= c2'*g(n); 
    assert bigThFrom(c1', c2', n0, f, g);    
  }

}