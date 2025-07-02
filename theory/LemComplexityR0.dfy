include "./math/ExpNat.dfy"
include "./math/FloorCeil.dfy"
include "./math/LemBoundsNat.dfy"
include "./math/LemFunction.dfy"
include "./math/LogNat.dfy"
include "./math/TypeR0.dfy"
include "./ComplexityNat.dfy"
include "./ComplexityR0.dfy"
include "./LemComplexity.dfy"

/**************************************************************************
  Lemmas about complexity of lifted functions
**************************************************************************/

module LemComplexityR0 { 
  import opened ExpNat
  import opened FloorCeil   
  import opened LemBoundsNat
  import opened LemFunction
  import opened LogNat  
  import opened TypeR0 
  import opened ComplexityR0

  /* BigTheta1 and bigTheta2 are equivalent definitions of Big Θ */
  
  lemma lem_bigTheta_def1EQLdef2(f:nat->R0, g:nat->R0)  
    ensures bigTheta1(f, g) <==> bigTheta2(f, g)
  {
    assert bigTheta1(f, g) ==> bigTheta2(f, g) by {
      assume {:axiom} bigTheta1(f, g);
      lem_bigTheta_def1IMPLdef2(f, g);
    }
    assert bigTheta2(f, g) ==> bigTheta1(f, g) by {
      assume {:axiom} bigTheta2(f, g);
      lem_bigTheta_def2IMPLdef1(f, g);
    }
  }

  lemma lem_bigTheta_def1IMPLdef2(f:nat->R0, g:nat->R0)  
    requires bigTheta1(f, g) 
    ensures  bigTheta2(f, g)
  {
    var c1:R0, n0_1:nat :| bigOmegaFrom(c1, n0_1, f, g) ; 
    assert H1: forall n:nat :: 0 <= n0_1 <= n ==> c1*g(n) <= f(n);

    var c2:R0, n0_2:nat :| bigOfrom(c2, n0_2, f, g) ; 
    assert H2: forall n:nat :: 0 <= n0_2 <= n ==> f(n) <= c2*g(n);

    var n0 := n0_1 + n0_2;
    forall n:nat | 0 <= n0 <= n
      ensures c1*g(n) <= f(n) <= c2*g(n)
    {
      assert c1*g(n) <= f(n) by { reveal H1; }
      assert f(n) <= c2*g(n) by { reveal H2; }
    }
    assert bigThetaFrom(c1, c2, n0, f, g);
  }

  lemma lem_bigTheta_def2IMPLdef1(f:nat->R0, g:nat->R0)  
    requires bigTheta2(f, g) 
    ensures  bigTheta1(f, g)
  {
    var c1:R0, c2:R0, n0:nat :| bigThetaFrom(c1, c2, n0, f, g); 
    assert H: forall n:nat :: 0 <= n0 <= n ==> c1*g(n) <= f(n) <= c2*g(n);

    assert A: bigO(f, g) by {
      forall n:nat | 0 <= n0 <= n
        ensures f(n) <= c2*g(n)
      {
        assert f(n) <= c2*g(n) by { reveal H; }
      }
      assert bigOfrom(c2, n0, f, g);
    }
    assert B: bigOmega(f, g) by {
      forall n:nat | 0 <= n0 <= n
        ensures c1*g(n) <= f(n)
      {
        assert c1*g(n) <= f(n) by { reveal H; }
      }
      assert bigOmegaFrom(c1, n0, f, g);
    }
    
    assert bigO(f, g) && bigOmega(f, g) by { reveal A, B; }
  }      

  /* Big O basic properties */

  // Reflexivity
  // f ∈ O(f)
  lemma lem_bigO_refl(f:nat->R0)  
    ensures bigO(f, f) 
  {  
    // we show that c=1.0 and n0=0
    assert forall n:nat :: 0 <= 0 <= n ==> f(n) <= 1.0*f(n);
    assert bigOfrom(1.0, 0, f, f);
  }

  // If f ∈ O(g) and a>0 then a*f ∈ O(g)
  lemma lem_bigO_constFactor(f:nat->R0, g:nat->R0, a:R0)  
    requires bigO(f, g) 
    requires a > 0.0 
    ensures  bigO(n => a*f(n), g) 
  {  
    var c:R0, n0:nat :| bigOfrom(c, n0, f, g);  
    assert forall n:nat :: 0 <= n0 <= n ==> f(n) <= c*g(n);
    
    // we show that c'=a*c and n0'=n0
    assert forall n:nat :: 0 <= n0 <= n ==> a*f(n) <= (a*c)*g(n);
    assert bigOfrom(a*c, n0, n => a*f(n), g);
  }

  // If f1 ∈ O(g1) and f2 ∈ O(g2) then f1+f2 ∈ O(g1+g2)
  lemma lem_bigO_sum(f1:nat->R0, g1:nat->R0, f2:nat->R0, g2:nat->R0)  
    requires bigO(f1, g1) 
    requires bigO(f2, g2) 
    ensures  bigO(n => f1(n)+f2(n), n => g1(n)+g2(n)) 
  {  
    var c1:R0, n1:nat :| bigOfrom(c1, n1, f1, g1);  
    assert forall n:nat :: 0 <= n1 <= n ==> f1(n) <= c1*g1(n);
    var c2:R0, n2:nat :| bigOfrom(c2, n2, f2, g2);  
    assert forall n:nat :: 0 <= n2 <= n ==> f2(n) <= c2*g2(n);   
    
    // we show that c=c1+c2 and n0=n1+n2
    assert forall n:nat :: 0 <= n1+n2 <= n ==> f1(n) + f2(n) <= c1*g1(n) + c2*g2(n);
    assert forall n:nat :: 0 <= n1+n2 <= n ==> f1(n) + f2(n) <= (c1+c2)*(g1(n) + g2(n));
    assert bigOfrom(c1+c2, n1+n2, n => f1(n)+f2(n), n => g1(n)+g2(n));
  }

  // If f1 ∈ O(g1) and f2 ∈ O(g2) then f1*f2 ∈ O(g1*g2)
  lemma lem_bigO_prod(f1:nat->R0, g1:nat->R0, f2:nat->R0, g2:nat->R0)  
    requires bigO(f1, g1) 
    requires bigO(f2, g2) 
    ensures  bigO(n => f1(n)*f2(n), n => g1(n)*g2(n)) 
  {  
    var c1:R0, n1:nat :| bigOfrom(c1, n1, f1, g1);  
    assert forall n:nat :: 0 <= n1 <= n ==> f1(n) <= c1*g1(n);
    var c2:R0, n2:nat :| bigOfrom(c2, n2, f2, g2);  
    assert forall n:nat :: 0 <= n2 <= n ==> f2(n) <= c2*g2(n);   
    
    // we show that c=c1*c2 and n0=n1+n2
    assert forall n:nat :: 0 <= n1+n2 <= n ==> f1(n)*f2(n) <= (c1*g1(n))*(c2*g2(n));
    assert forall n:nat :: 0 <= n1+n2 <= n ==> f1(n)*f2(n) <= (c1*c2)*(g1(n)*g2(n));
    assert bigOfrom(c1*c2, n1+n2, n => f1(n)*f2(n), n => g1(n)*g2(n));
  }

  // Transitivity
  // If f ∈ O(g) and g ∈ O(h) then f ∈ O(h)
  lemma lem_bigO_trans(f:nat->R0, g:nat->R0, h:nat->R0)  
    requires bigO(f, g) 
    requires bigO(g, h) 
    ensures  bigO(f, h) 
  {  
    var c1:R0, n1:nat :| bigOfrom(c1, n1, f, g);  
    assert forall n:nat :: 0 <= n1 <= n ==> f(n) <= c1*g(n);
    var c2:R0, n2:nat :| bigOfrom(c2, n2, g, h);  
    assert forall n:nat :: 0 <= n2 <= n ==> g(n) <= c2*h(n);   
    
    // we show that c=c1*c2 and n0=n1+n2
    forall n:nat | 0 <= n1+n2 <= n
      ensures f(n) <= c1*c2*h(n)
    {
      if 0 <= n1+n2 <= n {
        calc {
             f(n); 
          <= c1*g(n);
          <= { assert g(n) <= c2*h(n); } 
             c1*c2*h(n);         
        }
      }
    }
    assert bigOfrom(c1*c2, n1+n2, f, h);
  }

  // TODO: prove If f ∈ O(g) then f+g ∈ O(g)

  /* Common growth rates comparison */

  // log2(n) ∈ O(n) 
  lemma {:axiom} lem_bigO_logBigOlin()
    ensures bigO(logGrowth(), linGrowth()) 

  // log2(n+1) ∈ O(n) 
  lemma {:axiom} lem_bigO_logBigOlinV2()
    ensures bigO(logGrowth2(), linGrowth())

  // n ∈ O(n^2) 
  lemma {:axiom} lem_bigO_linBigOquad()
    ensures bigO(linGrowth(), quadGrowth()) 

  // n^2 ∈ O(2^n)  
  lemma {:axiom} lem_bigO_quadBigOexp()
    ensures bigO(quadGrowth(), expGrowth())

  // n ∈ O(2^n)  
  lemma {:axiom} lem_bigO_linBigOexp()
    ensures bigO(linGrowth(), expGrowth()) 

}