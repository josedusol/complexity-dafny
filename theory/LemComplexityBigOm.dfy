include "./math/ExpNat.dfy"
include "./math/ExpReal.dfy"
include "./math/FloorCeil.dfy"
include "./math/LemBoundsNat.dfy"
include "./math/LemFunction.dfy"
include "./math/Log2Nat.dfy"
include "./math/Log2Real.dfy"
include "./math/LogReal.dfy"
include "./math/MaxMin.dfy"
include "./math/TypeR0.dfy"
include "./Complexity.dfy"

/******************************************************************************
  Lemmas of Big Omega Notation
******************************************************************************/

module LemComplexityBigOm {

  import EN = ExpNat
  import opened ExpReal
  import opened FloorCeil   
  import opened LemBoundsNat
  import opened LemFunction
  import LN = Log2Nat
  import opened Log2Real
  import opened LogReal
  import opened MaxMin
  import opened TypeR0 
  import opened Complexity

  /******************************************************************************
    Ω basic properties
  ******************************************************************************/

  // Reflexivity
  // f ∈ Ω(f)
  lemma lem_bigOm_refl(f:nat->R0)  
    ensures f in Om(f) 
  {  
    var c:R0, n0:nat := 1.0, 0;
    assert forall n:nat :: 0 <= n0 <= n ==> f(n) >= c*f(n);
    assert bigOmFrom(c, n0, f, f);
  }  

  // Transitivity
  // f ∈ Ω(g) ∧ g ∈ Ω(h) ⟹ f ∈ Ω(h)
  lemma lem_bigOm_trans(f:nat->R0, g:nat->R0, h:nat->R0)  
    requires f in Om(g) 
    requires g in Om(h)  
    ensures  f in Om(h)  
  {  
    var c1:R0, n1:nat :| c1 > 0.0 && bigOmFrom(c1, n1, f, g);  
    assert H1: forall n:nat :: 0 <= n1 <= n ==> c1*g(n) <= f(n);
    var c2:R0, n2:nat :| c2 > 0.0 && bigOmFrom(c2, n2, g, h);  
    assert H2: forall n:nat :: 0 <= n2 <= n ==> c2*h(n) <= g(n);   
    
    var c:R0, n0:nat := c1*c2, n1+n2;
    forall n:nat | 0 <= n0 <= n
      ensures c*h(n) <= f(n)
    {
      calc {
           f(n); 
        >= { reveal H1; }
           c1*g(n);
        >= { reveal H2; } 
           c1*c2*h(n);     
        == c*h(n);         
      }
    }
    assert c > 0.0 && bigOmFrom(c, n0, f, h);
  }  

  // f ∈ O(g) ⟹ f+g ∈ Ω(g)
  lemma lem_bigOm_sumSimp(f:nat->R0, g:nat->R0)  
    requires f in O(g) 
    ensures  (n => f(n)+g(n)) in Om(g)  
  {
    var c:R0, n0:nat :| c > 0.0 && bigOfrom(c, n0, f, g);  
    assert H1: forall n:nat :: 0 <= n0 <= n ==> f(n) <= c*g(n);

    // prove f+g ∈ Ω(g)
    var c2:R0, n2:nat := 1.0, 0;
    forall n:nat | 0 <= n2 <= n
      ensures c2*g(n) <= f(n) + g(n)
    {
      calc {
           c2*g(n); 
        <= f(n) + g(n);        
      }
    }  
    assert c2 > 0.0 && bigOmFrom(c2, n2, n => f(n)+g(n), g);
  }

  // f ∈ O(g) ⟹ g ∈ Ω(f+g)
  lemma lem_bigOm_sumSynth(f:nat->R0, g:nat->R0)  
    requires f in O(g) 
    ensures  g in Om(n => f(n)+g(n))  
  {
    var c:R0, n0:nat :| c > 0.0 && bigOfrom(c, n0, f, g);  
    assert H1: forall n:nat :: 0 <= n0 <= n ==> f(n) <= c*g(n);

    var c1:R0, n1:nat := 1.0/(c+1.0), n0;
    forall n:nat | 0 <= n1 <= n
      ensures c1*(f(n) + g(n)) <= g(n)
    {
      calc {
           g(n);       
        == c1*(c+1.0)*g(n);
        == c1*(c*g(n) + g(n));
        >= { reveal H1; }
           c1*(f(n) + g(n));
      }
    }  
    assert c1 > 0.0 && bigOmFrom(c1, n1, g, n => f(n)+g(n));
  }  

  // Upward closure wrto <=
  // lo(n) <= f(n) eventually ∧ lo ∈ Ω(h) ⟹ f ∈ Ω(h)
  lemma lem_bigOm_LEQupwardClosure(f:nat->R0, lo:nat->R0, h:nat->R0, n1:nat)  
    requires forall n:nat :: n >= n1 ==> lo(n) <= f(n)
    requires lo in Om(h)
    ensures  f  in Om(h)
  {  
    var c2:R0, n2:nat :| c2 > 0.0 && bigOmFrom(c2, n2, lo, h);
    assert H1: forall n:nat :: 0 <= n2 <= n ==> c2*h(n) <= lo(n);

    var c:R0, n0:nat := c2, max(n1, n2);
    forall n:nat | 0 <= n0 <= n
      ensures c*h(n) <= f(n)
    {
      calc {
           c2*h(n);
        <= lo(n);
        <= f(n);        
      }
      assert c2*h(n) <= f(n);
    }
    assert bigOmFrom(c, n0, f, h);
  }

  // The base of log doesn't change asymptotics
  // b1,b2 > 0 ⟹ h ∈ Ω(log_b1) ⟺ h ∈ Ω(log_b2)
  lemma lem_bigOm_logBase(b1:real, b2:real, h:nat->R0)  
    requires b1 > 1.0 && b2 > 1.0
    requires h in Om(logGrowth(b1))
    ensures  h in Om(logGrowth(b2))
  {
    var c1:R0, n0:nat :| c1 > 0.0 && bigOmFrom(c1, n0, h, logGrowth(b1));
    assert H1: forall n:nat :: 0 <= n0 <= n ==> c1*logGrowth(b1)(n) <= h(n); 

    lem_log_NonNegative(b2, b1);
    var G:R0 := log(b2, b1); 
    assert G > 0.0 by { lem_log_Positive(b2, b1); }
    var c1':R0, n0':nat := c1/G, n0+1;
    forall n:nat | 0 <= n0' <= n
      ensures c1'*logGrowth(b2)(n) <= h(n)
    {
      calc {
           c1'*logGrowth(b2)(n);
        == c1'*log(b2, n as R0); 
        == c1*(log(b2, n as R0)/G);
        == { lem_log_ChangeOfBase(b1, b2, n as R0); }    
           c1*log(b1, n as R0);
        <= { reveal H1; }
           h(n);   
      }
    }
    assert c1' > 0.0 && bigOmFrom(c1', n0', h, logGrowth(b2));
  } 

  // b1,b2 > 0 ⟹ Ω(log_b1) = Ω(log_b2)
  lemma lem_bigOmSet_logBase(b1:real, b2:real)  
    requires b1 > 1.0 && b2 > 1.0
    ensures  Om(logGrowth(b1)) == Om(logGrowth(b2))
  {
    forall h:nat->R0
      ensures h in Om(logGrowth(b1)) <==> h in Om(logGrowth(b2))
    {
      assert h in Om(logGrowth(b1)) ==> h in Om(logGrowth(b2)) by { 
        if h in Om(logGrowth(b1)) {
          lem_bigOm_logBase(b1, b2, h); 
        }
      }
      assert h in Om(logGrowth(b2)) ==> h in Om(logGrowth(b1)) by { 
        if h in Om(logGrowth(b2)) {
          lem_bigOm_logBase(b2, b1, h); 
        }
      }      
    }
  }

  // Ω(f) = Ω(g) ⟹ f ∈ Ω(g) ∧ g ∈ Ω(f)
  lemma lem_bigOmSet_mutualInc(f:nat->R0, g:nat->R0)  
    requires Om(f) == Om(g)
    ensures  f in Om(g) && g in Om(f)
  { 
    assert f in Om(f) by { lem_bigOm_refl(f); }
    assert g in Om(g) by { lem_bigOm_refl(g); }
  }

  // Congruence of membership with respect to equality
  // Ω(f) = Ω(g) ∧ f ∈ Ω(h) ⟹ g ∈ Ω(h)
  lemma lem_bigOmSet_congEq(f:nat->R0, g:nat->R0, h:nat->R0)  
    requires Om(f) == Om(g)
    requires f in Om(h)
    ensures  g in Om(h) 
  {
    lem_bigOmSet_mutualInc(f, g);
    assert g in Om(f);
    assert f in Om(h);
    lem_bigOm_trans(g, f, h);
  }

  // f ∈ O(g) ⟹ Ω(f+g) = Ω(g)
  lemma lem_bigOmSet_sumSimp(f:nat->R0, g:nat->R0)  
    requires f in O(g) 
    ensures  Om(n => f(n)+g(n)) == Om(g)
  {
    // prove Ω(f+g) ⊆ Ω(g)
    forall h:nat->R0 | h in Om(n => f(n)+g(n)) 
      ensures h in Om(g) 
    {
      assert h in Om(n => f(n)+g(n));  
      assert (n => f(n)+g(n)) in Om(g) 
        by { lem_bigOm_sumSimp(f, g); }
      lem_bigOm_trans(h, n => f(n)+g(n), g);  
    }    

    // prove Ω(g) ⊆ Ω(f+g)
    forall h:nat->R0 | h in Om(g)
      ensures h in Om(n => f(n)+g(n)) 
    {
      assert h in Om(g);  
      assert g in Om(n => f(n)+g(n))
        by { lem_bigOm_sumSynth(f, g); }
      lem_bigOm_trans(h, g, n => f(n)+g(n));  
    }      
  }

  /******************************************************************************
    Comparison of common growth rates according to Ω
  ******************************************************************************/

  // f ∈ Ω(0) 
  lemma lem_bigOm_anyBigOmZero(f:nat->R0)
    ensures f in Om(zeroGrowth()) 
  {
    var c:R0, n0:nat := 1.0, 0;
    forall n:nat | 0 <= n0 <= n 
      ensures c*zeroGrowth()(n) <= f(n)
    {
      calc {
           f(n);
        >= c*0.0;
        == c*zeroGrowth()(n);             
      }
    }
    assert c > 0.0 && bigOmFrom(c, n0, f, zeroGrowth());
  } 

  // 1 ∈ Ω(0) 
  lemma lem_bigOm_constBigOmZero()
    ensures constGrowth() in Om(zeroGrowth()) 
  {
    lem_bigOm_anyBigOmZero(constGrowth());
  }   

  /******************************************************************************
    Inclusion hierarchy: smaller growth functions contain bigger-growth functions.

      Ω(b^n) ⊆ ... ⊆ Ω(3^n) ⊆ Ω(2^n) 
             ⊆ Ω(n^k) ⊆ ... ⊆ Ω(n^3) ⊆ Ω(n^2) 
             ⊆ Ω(log_b) ⊆ Ω(1) ⊆ Ω(0)

    Proving Ω(f) ⊆ Ω(g) amounts to proving f ∈ Ω(g) and using transitivity.               
  ******************************************************************************/

  // Ω(1) ⊆ Ω(0) 
  lemma lem_bigOmSet_constLEQzero(f:nat->R0)
    ensures Om(constGrowth()) <= Om(zeroGrowth()) 
  {
    forall h:nat->R0 | h in Om(constGrowth()) 
      ensures h in Om(zeroGrowth()) 
    {
      calc {
            h in Om(constGrowth());
        ==> { lem_bigOm_constBigOmZero(); 
              lem_bigOm_trans(h, constGrowth(), zeroGrowth()); }
            h in Om(zeroGrowth());
      } 
    } 
  }

}