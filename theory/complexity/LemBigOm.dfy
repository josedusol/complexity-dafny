include "../math/ExpNat.dfy"
include "../math/ExpReal.dfy"
include "../math/FloorCeil.dfy"
include "../math/Function.dfy"
include "../math/LemBoundsNat.dfy"
include "../math/LemFunction.dfy"
include "../math/Log2Nat.dfy"
include "../math/Log2Real.dfy"
include "../math/LogReal.dfy"
include "../math/MaxMin.dfy"
include "../math/TypeR0.dfy"
include "./Asymptotics.dfy"

/******************************************************************************
  Lemmas of Big Omega
******************************************************************************/

module LemBigOm {

  import ExpN = ExpNat
  import ExpR = ExpReal
  import opened FloorCeil   
  import opened Function
  import opened LemBoundsNat
  import opened LemFunction
  import Log2N = Log2Nat
  import Log2R = Log2Real
  import LogR  = LogReal
  import opened MaxMin
  import opened TypeR0 
  import opened Asymptotics

  /******************************************************************************
    Order properties on functions
  ******************************************************************************/
  
  // Ω behaves like a preorder (refl + trans) on functions

  // Reflexivity
  // f ∈ Ω(f)
  lemma lem_Refl(f:nat->R0)  
    ensures f in Om(f) 
  {  
    var c:R0, n0:nat := 1.0, 0;
    assert forall n:nat :: 0 <= n0 <= n ==> f(n) >= c*f(n);
    assert bigOmFrom(c, n0, f, f);
  }  

  // Transitivity
  // f ∈ Ω(g) ∧ g ∈ Ω(h) ⟹ f ∈ Ω(h)
  lemma lem_Trans(f:nat->R0, g:nat->R0, h:nat->R0)  
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

  // Ω is not antisymmetric on functions themselves, e.g. let f(n)=n and g(n)=2n,
  // then we have f ∈ Ω(g) and g ∈ Ω(f) but f ≠ g.
  // However, we have the following property

  // Antisymmetry up to class equivalence
  // f ∈ Ω(g) ∧ g ∈ Ω(f) ⟹ Ω(f) = Ω(h)
  lemma lem_AntiSym(f:nat->R0, g:nat->R0)  
    requires f in Om(g) 
    requires g in Om(f)  
    ensures  Om(f) == Om(g)  
    // TODO

  /******************************************************************************
    Structural properties
  ******************************************************************************/

  // Idempotency under addition
  // f + f ∈ Ω(f)
  lemma lem_SumIdemp(f:nat->R0)  
    ensures (n => f(n)+f(n)) in Om(f) 
  {
    assert f in Om(f) 
      by { lem_Refl(f); }
    assert (n => f(n)+f(n)) == (n => 2.0*f(n))
      by { lem_Exten(n => f(n)+f(n), n => 2.0*f(n)); }
    assert (n => 2.0*f(n)) in Om(f) 
      by { lem_Scale(f, f, 2.0); }
  }  

  // Power of two
  // f*f ∈ Ω(f^2)
  lemma lem_Pow2(f:nat->R0)  
    ensures (n => f(n)*f(n)) in Om(n => ExpR.exp(f(n), 2.0)) 
  {
    assert (n => f(n)*f(n)) in Om(n => f(n)*f(n)) 
      by { lem_Refl(n => f(n)*f(n)); }
    assert (n => f(n)*f(n)) == (n => ExpR.exp(f(n), 2.0))
      by { ExpR.lem_Pow2Auto();
           lem_Exten(n => f(n)*f(n), n => ExpR.exp(f(n), 2.0)); }
  } 

  /******************************************************************************
    Closure properties
  ******************************************************************************/

  // These describe how the classes behave under operations

  // Closure under scaling
  // f ∈ Ω(g) ∧ a > 0 ⟹ a*f ∈ Ω(g)
  lemma lem_Scale(f:nat->R0, g:nat->R0, a:R0)
    requires f in Om(g) 
    requires a > 0.0 
    ensures  (n => a*f(n)) in Om(g) 
    // TODO

  // Closure under addition
  // f1 ∈ Ω(g1) ∧ f2 ∈ Ω(g2) ⟹ f1+f2 ∈ Ω(g1+g2)
  lemma lem_Sum(f1:nat->R0, g1:nat->R0, f2:nat->R0, g2:nat->R0)  
    requires f1 in Om(g1) 
    requires f2 in Om(g2) 
    ensures  (n => f1(n)+f2(n)) in Om(n => g1(n)+g2(n)) 
    // TODO

  // Closure under addition within the same class
  // f1 ∈ Ω(g) ∧ f2 ∈ Ω(g) ⟹ f1 + f2 ∈ Ω(g)
  lemma lem_SumSameClass(f1:nat->R0, f2:nat->R0, g:nat->R0)  
    requires f1 in Om(g) 
    requires f2 in Om(g) 
    ensures  (n => f1(n)+f2(n)) in Om(g) 
  {  
    lem_Sum(f1, g, f2, g);  
    assert (n => f1(n)+f2(n)) in Om(n => g(n)+g(n));
    assert (n => g(n)+g(n))   in Om(g) by { lem_SumIdemp(g); }
    lem_Trans(n => f1(n)+f2(n), n => g(n)+g(n), g);
  }

  // f ∈ O(g) ⟹ f+g ∈ Ω(g)
  lemma lem_SumSimpl(f:nat->R0, g:nat->R0)  
    requires f in O(g) 
    ensures  (n => f(n)+g(n)) in Om(g)  
  {
    var c:R0, n0:nat :| c > 0.0 && bigOhFrom(c, n0, f, g);  
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
  lemma lem_SumSynth(f:nat->R0, g:nat->R0)  
    requires f in O(g) 
    ensures  g in Om(n => f(n)+g(n))  
  {
    var c:R0, n0:nat :| c > 0.0 && bigOhFrom(c, n0, f, g);  
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
  lemma lem_LEQupwardClosure(f:nat->R0, lo:nat->R0, h:nat->R0, n1:nat)  
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

  /******************************************************************************
    Monotonicity properties
  ******************************************************************************/

  // f ∈ Ω(g) ⟹ Ω(f) ⊆ Ω(g)
  lemma lem_MonoIncr(f:nat->R0, g:nat->R0)  
    requires f in Om(g)
    ensures  Om(f) <= Om(g) 
  {
    forall h:nat->R0 | h in Om(f) 
      ensures h in Om(g) 
    {
      calc {
            h in Om(f);
        ==> { assert f in Om(g); 
              lem_Trans(h, f, g); }
            h in Om(g);
      }
    } 
  }

  /******************************************************************************
    Closure properties from the set-theoretic view
  ******************************************************************************/
  
  // Each result follows from it's corresponding membership version property

  // lem_bigOm_scaling lifted to sets
  // f ∈ Ω(g) ∧ a > 0 ⟹ Ω(a*f) ⊆ Ω(g)
  lemma lem_ScaleSet(f:nat->R0, g:nat->R0, a:R0)
    requires f in Om(g) 
    requires a > 0.0 
    ensures  Om(n => a*f(n)) <= Om(g) 
  {  
    assert (n => a*f(n)) in Om(g) 
      by { lem_Scale(f, g, a); }    
    lem_MonoIncr(n => a*f(n), g);
  }

  // f ∈ O(g) ⟹ Ω(f+g) = Ω(g)
  lemma lem_SumSimplSet(f:nat->R0, g:nat->R0)  
    requires f in O(g)
    ensures  Om(n => f(n)+g(n)) == Om(g)
  {
    // prove Ω(f+g) ⊆ Ω(g)
    forall h:nat->R0 | h in Om(n => f(n)+g(n)) 
      ensures h in Om(g) 
    {
      assert h in Om(n => f(n)+g(n));  
      assert (n => f(n)+g(n)) in Om(g) 
        by { lem_SumSimpl(f, g); }
      lem_Trans(h, n => f(n)+g(n), g);  
    }    

    // prove Ω(g) ⊆ Ω(f+g)
    forall h:nat->R0 | h in Om(g)
      ensures h in Om(n => f(n)+g(n)) 
    {
      assert h in Om(g);  
      assert g in Om(n => f(n)+g(n))
        by { lem_SumSynth(f, g); }
      lem_Trans(h, g, n => f(n)+g(n));  
    }      
  }

  /******************************************************************************
    Equivalence properties (on classes)
  ******************************************************************************/

  // Ω(f) = Ω(g) induces an equivalence relation on functions

  // Equivalence of representatives
  // Ω(f) = Ω(g) ⟹ f ∈ Ω(g) ∧ g ∈ Ω(f)
  lemma lem_EqRepr(f:nat->R0, g:nat->R0)  
    requires Om(f) == Om(g)
    ensures  f in Om(g) && g in Om(f)
  { 
    assert f in Om(f) by { lem_Refl(f); }
    assert g in Om(g) by { lem_Refl(g); }
  }

  /******************************************************************************
    Congruence properties
  ******************************************************************************/

  // These show that equivalence is preserved under operations or relations

  // Congruence of membership
  // Ω(f) = Ω(g) ∧ f ∈ Ω(h) ⟹ g ∈ Ω(h)
  lemma lem_CongEq(f:nat->R0, g:nat->R0, h:nat->R0)  
    requires Om(f) == Om(g)
    requires f in Om(h)
    ensures  g in Om(h) 
  {
    lem_EqRepr(f, g);
    assert g in Om(f);
    assert f in Om(h);
    lem_Trans(g, f, h);
  }

  // Congruence of order
  // Ω(f) = Ω(g) ∧ Ω(h) = Ω(k) ∧ f ∈ Ω(h) ⟹ g ∈ Ω(k)
  lemma lem_CongOrder(f:nat->R0, g:nat->R0, h:nat->R0, k:nat->R0)  
    requires Om(f) == Om(g)
    requires Om(h) == Om(k)
    requires f in Om(h)
    ensures  g in Om(k)  
    // TODO

  /******************************************************************************
    Zero functions and the class Ω(0)
  ******************************************************************************/

  // Any function eventually zero is Ω(0)
  // Note: the reverse doesn't hold, because any function is in Ω(0)
  lemma lem_EventuallyZeroGrowth(f:nat->R0, n0:nat)  
    requires EventuallyZero(f, n0)
    ensures  f in Om(zeroGrowth())
  {  
    var c:R0, n0:nat := 1.0, n0;
    forall n:nat | 0 <= n0 <= n
      ensures c*zeroGrowth()(n) <= f(n)
    {
      calc {
           c*zeroGrowth()(n);
        == c*0.0;  
        == 0.0;  
        <= f(n);        
      }
    }
    assert c > 0.0 && bigOmFrom(c, n0, f, zeroGrowth());
  }

  // Zero function is Ω(0)
  lemma lem_ZeroGrowth(f:nat->R0)  
    requires forall n:nat :: f(n) == 0.0
    ensures  f in Om(zeroGrowth())
  {  
    lem_EventuallyZeroGrowth(f, 0); 
  }

  /******************************************************************************
    Const functions and the class Ω(1)
  ******************************************************************************/

  // Any function eventually non-zero const is Ω(1)
  lemma lem_EventuallyConstGrowth(f:nat->R0, a:R0, n0:nat)  
    requires a > 0.0
    requires EventuallyConst(f, a, n0)
    ensures  f in Om(constGrowth())
  {  
    var c:R0, n0:nat := a/2.0, n0;
    forall n:nat | 0 <= n0 <= n
      ensures c*constGrowth()(n) <= f(n)
    {
      calc {
           c*constGrowth()(n);
        == c*1.0; 
        == a/2.0; 
        <= f(n);         
      }
    }
    assert c > 0.0 && bigOmFrom(c, n0, f, constGrowth());
  }

  // Any non-zero const function is Ω(1)
  lemma lem_ConstGrowth(f:nat->R0, a:R0)  
    requires a > 0.0
    requires forall n:nat :: f(n) == a
    ensures  f in Om(constGrowth())
  {  
    lem_EventuallyConstGrowth(f, a, 0);
  }  

  // Any function eventually bounded below by a non-zero const is Ω(1)
  lemma lem_EventuallyBoundConstGrowth(f:nat->R0, a:R0, n0:nat)  
    requires a > 0.0
    requires EventuallyConstBoundBelow(f, a, n0)
    ensures  f in Om(constGrowth())
  {  
    var c:R0, n0:nat := a, n0;
    forall n:nat | 0 <= n0 <= n
      ensures c*constGrowth()(n) <= f(n)
    {
      calc {
           f(n); 
        >= a;
        >= a*1.0;      
        == c*constGrowth()(n);         
      }
    }
    assert c > 0.0 && bigOmFrom(c, n0, f, constGrowth());
  }

  // Reverse direction of lem_EventuallyBoundConstGrowth
  // Any function in Ω(1) is eventually bounded below by a non-zero const
  lemma lem_EventuallyBoundConstGrowthREV(f:nat->R0)  
    requires f in Om(constGrowth())  
    ensures  exists a, n0 :: a > 0.0 && EventuallyConstBoundBelow(f, a, n0)
  {  
    var c:R0, n1:nat :| c > 0.0 && bigOmFrom(c, n1, f, constGrowth());  
    assert H1: forall n:nat :: 0 <= n1 <= n ==> c*constGrowth()(n) <= f(n);

    forall n:nat | n1 <= n
      ensures f(n) >= c
    { }
    assert c > 0.0 && EventuallyConstBoundBelow(f, c, n1);
    assert exists a, n0 :: a > 0.0 && EventuallyConstBoundBelow(f, a, n0);   
  }   

  // Join previous facts into an equivalence
  // This serves as a characterization of the Ω(1) class
  // f in Ω(1) ⟺ f eventually bounded below by a non-zero const
  lemma lem_EventuallyBoundConstGrowthIFF(f:nat->R0)  
    ensures f in Om(constGrowth()) <==> exists n0, a :: a > 0.0 && EventuallyConstBoundBelow(f, a, n0)
  {  
    assert f in Om(constGrowth()) ==> exists n0, a :: a > 0.0 && EventuallyConstBoundBelow(f, a, n0) by {
      if f in Om(constGrowth()) { 
        lem_EventuallyBoundConstGrowthREV(f); 
      }
    }
    assert (exists a, n0 :: a > 0.0 && EventuallyConstBoundBelow(f, a, n0)) ==> f in Om(constGrowth()) by {
      if exists a, n0 :: a > 0.0 && EventuallyConstBoundBelow(f, a, n0) {
        var a, n0 :| a > 0.0 && EventuallyConstBoundBelow(f, a, n0);
        lem_EventuallyBoundConstGrowth(f, a, n0);
      }
    }     
  }  

  /******************************************************************************
    Logarithms and the class Ω(log_b)
  ******************************************************************************/

  // The base of log doesn't change asymptotics
  // b1,b2 > 0 ⟹ h ∈ Ω(log_b1) ⟺ h ∈ Ω(log_b2)
  lemma lem_LogBase(b1:real, b2:real, h:nat->R0)  
    requires b1 > 1.0 && b2 > 1.0
    requires h in Om(logGrowth(b1))
    ensures  h in Om(logGrowth(b2))
  {
    var c1:R0, n0:nat :| c1 > 0.0 && bigOmFrom(c1, n0, h, logGrowth(b1));
    assert H1: forall n:nat :: 0 <= n0 <= n ==> c1*logGrowth(b1)(n) <= h(n); 

    LogR.lem_NonNegative(b2, b1);
    var G:R0 := LogR.log(b2, b1); 
    assert G > 0.0 by { LogR.lem_Positive(b2, b1); }
    var c1':R0, n0':nat := c1/G, n0+1;
    forall n:nat | 0 <= n0' <= n
      ensures c1'*logGrowth(b2)(n) <= h(n)
    {
      calc {
           c1'*logGrowth(b2)(n);
        == c1'*LogR.log(b2, n as R0); 
        == c1*(LogR.log(b2, n as R0)/G);
        == { LogR.lem_ChangeOfBase(b1, b2, n as R0); }    
           c1*LogR.log(b1, n as R0);
        <= { reveal H1; }
           h(n);   
      }
    }
    assert c1' > 0.0 && bigOmFrom(c1', n0', h, logGrowth(b2));
  } 

  // b1,b2 > 0 ⟹ Ω(log_b1) = Ω(log_b2)
  lemma lem_LogBaseSet(b1:real, b2:real)  
    requires b1 > 1.0 && b2 > 1.0
    ensures  Om(logGrowth(b1)) == Om(logGrowth(b2))
  {
    forall h:nat->R0
      ensures h in Om(logGrowth(b1)) <==> h in Om(logGrowth(b2))
    {
      assert h in Om(logGrowth(b1)) ==> h in Om(logGrowth(b2)) by { 
        if h in Om(logGrowth(b1)) {
          lem_LogBase(b1, b2, h); 
        }
      }
      assert h in Om(logGrowth(b2)) ==> h in Om(logGrowth(b1)) by { 
        if h in Om(logGrowth(b2)) {
          lem_LogBase(b2, b1, h); 
        }
      }      
    }
  }  

  /******************************************************************************
    Membership between common growth rates
  ******************************************************************************/

  // f ∈ Ω(0) 
  lemma lem_AnyInZero(f:nat->R0)
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
  lemma lem_ConstInZero()
    ensures constGrowth() in Om(zeroGrowth()) 
  {
    lem_AnyInZero(constGrowth());
  }   

  // TODO

  /******************************************************************************
    Non-membership of common growth rates
  ******************************************************************************/

  // TODO

  /******************************************************************************
    Inclusion hierarchy: smaller growth functions contain bigger-growth functions.
    Reverse of O inclusion hierarchy.

      Ω(0) ⊇ Ω(1) ⊇ Ω(log_b)
                  ⊇ Ω(n^1) ⊇ Ω(n^2) ⊇ ... ⊇ Ω(n^k) 
                  ⊇ Ω(2^n) ⊇ Ω(3^n) ⊇ ... ⊇ Ω(b^n) 

    Proving Ω(f) ⊆ Ω(g) amounts to proving f ∈ Ω(g) and using transitivity, which
    is exactly what lem_MonoIncr give us.                            
  ******************************************************************************/

  // Ω(1) ⊆ Ω(0) 
  lemma lem_ConstLeqZero(f:nat->R0)
    ensures Om(constGrowth()) <= Om(zeroGrowth()) 
  {
    lem_ConstInZero();
    lem_MonoIncr(constGrowth(), zeroGrowth());
  }

  // TODO

}