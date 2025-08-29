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
    Mapping of O asymptotic results between unlifted and lifted functions
  ******************************************************************************/

  // If we prove f ∈ O(g) for f,g:nat->nat then we can extend
  // the result for the lifted versions f',g':nat->R0.
  lemma lem_bigOtoBigOR0(f:nat->nat, g:nat->nat)  
    requires f in O(g)
    ensures  liftToR0(f) in CR0.O(liftToR0(g))
  {    
    var c:nat, n0:nat :| c > 0 && bigOfrom(c, n0, f, g);  
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
    requires liftToR0(f) in CR0.O(liftToR0(g))
    ensures  f in O(g)
  { 
    var c:R0, n0:nat :| c > 0.0 && CR0.bigOfrom(c, n0, liftToR0(f), liftToR0(g));
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
    Mapping of Ω asymptotic results between unlifted and lifted functions
  ******************************************************************************/

  lemma lem_bigOmToBigOmR0(f:nat->nat, g:nat->nat)  
    requires f in Om(g) 
    ensures  liftToR0(f) in CR0.Om(liftToR0(g))
  {    
    var c:nat, n0:nat :| c > 0 && bigOmFrom(c, n0, f, g);  
    assert forall n:nat :: 0 <= n0 <= n ==> c*g(n) <= f(n);

    assert forall n:nat :: liftToR0(f)(n) == f(n) as R0;
    assert forall n:nat :: liftToR0(g)(n) == g(n) as R0;

    var c':R0 := c as R0;  // just view c:nat as a R0 number
    assert forall n:nat :: 0 <= n0 <= n ==> c'*liftToR0(g)(n) <= liftToR0(f)(n); 
    assert CR0.bigOmFrom(c', n0, liftToR0(f), liftToR0(g));
  }

  // This cant be proved anymore with the new O definition
  // lemma lem_bigOmR0toBigOm(f:nat->nat, g:nat->nat)  
  //   requires liftToR0(f) in CR0.Om(liftToR0(g))
  //   ensures  f in Om(g)

  /******************************************************************************
    Mapping of Θ asymptotic results between unlifted and lifted functions
  ******************************************************************************/

  lemma lem_bigTh2toBigTh2R0(f:nat->nat, g:nat->nat)  
    requires bigTh2(f, g)
    ensures  CR0.bigTh2(liftToR0(f), liftToR0(g))
  {
    assert bigOm(f, g) && bigO(f, g);
    lem_bigOmToBigOmR0(f, g); 
    lem_bigOtoBigOR0(f, g); 
  }
  
  // This cant be proved anymore with the new Θ definition
  // lemma lem_bigTh2R0toBigTh2(f:nat->nat, g:nat->nat)  
  //   requires CR0.bigTh2(liftToR0(f), liftToR0(g))
  //   ensures  bigTh2(f, g)

  lemma lem_bigThtoBigThR0(f:nat->nat, g:nat->nat)  
    requires f in Th(g) 
    ensures  liftToR0(f) in CR0.Th(liftToR0(g)) 
  {
    var c1:nat, c2:nat, n0:nat :| c1 > 0 && c2 > 0 && bigThFrom(c1, c2, n0, f, g);  
    assert forall n:nat :: 0 <= n0 <= n ==> c1*g(n) <= f(n) <= c2*g(n);

    assert forall n:nat :: liftToR0(f)(n) == f(n) as R0;
    assert forall n:nat :: liftToR0(g)(n) == g(n) as R0;

    var c1':R0 := c1 as R0;  // just view c1,c2:nat as R0 numbers
    var c2':R0 := c2 as R0;  
    assert forall n:nat :: 0 <= n0 <= n ==> c1'*liftToR0(g)(n) <= liftToR0(f)(n) <= c2'*liftToR0(g)(n); 
    assert CR0.bigThFrom(c1', c2', n0, liftToR0(f), liftToR0(g));
  } 
  
  // This cant be proved anymore with the new Θ definition
  // lemma lem_bigThR0toBigTh(f:nat->nat, g:nat->nat)  
  //   requires liftToR0(f) in CR0.Th(liftToR0(g))
  //   ensures  f in Th(g) 

}