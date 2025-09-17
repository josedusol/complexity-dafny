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
  Lemmas of Big Oh
******************************************************************************/

module LemBigOh {

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
  
  // O behaves like a preorder (refl + trans) on functions

  // Reflexivity
  // f ∈ O(f)
  lemma lem_Refl(f:nat->R0)  
    ensures f in O(f) 
  {  
    var c:R0, n0:nat := 1.0, 0;
    assert forall n:nat :: 0 <= n0 <= n ==> f(n) <= c*f(n);
    assert bigOhFrom(c, n0, f, f);
  }

  // Transitivity
  // f ∈ O(g) ∧ g ∈ O(h) ⟹ f ∈ O(h)
  lemma lem_Trans(f:nat->R0, g:nat->R0, h:nat->R0)  
    requires f in O(g) 
    requires g in O(h)  
    ensures  f in O(h)  
  {  
    var c1:R0, n1:nat :| c1 > 0.0 && bigOhFrom(c1, n1, f, g);  
    assert forall n:nat :: 0 <= n1 <= n ==> f(n) <= c1*g(n);
    var c2:R0, n2:nat :| c2 > 0.0 && bigOhFrom(c2, n2, g, h);  
    assert forall n:nat :: 0 <= n2 <= n ==> g(n) <= c2*h(n);   
    
    var c:R0, n0:nat := c1*c2, n1+n2;
    forall n:nat | 0 <= n0 <= n
      ensures f(n) <= c*h(n)
    {
      calc {
           f(n); 
        <= c1*g(n);
        <= { assert g(n) <= c2*h(n); } 
           c1*c2*h(n);     
        == c*h(n);         
      }
    }
    assert bigOhFrom(c, n0, f, h);
  }  

  // O is not antisymmetric on functions themselves, e.g. let f(n)=n and g(n)=2n, 
  // then we have f ∈ O(g) and g ∈ O(f) but f ≠ g.
  // However, we have the following property

  // Antisymmetry up to class equivalence
  // f ∈ O(g) ∧ g ∈ O(f) ⟹ O(f) = O(h)
  lemma lem_AntiSym(f:nat->R0, g:nat->R0)  
    requires f in O(g) 
    requires g in O(f)  
    ensures  O(f) == O(g)  
    // TODO

  /******************************************************************************
    Structural properties
  ******************************************************************************/

  // Idempotency under addition
  // f + f ∈ O(f)
  lemma lem_SumIdemp(f:nat->R0)  
    ensures (n => f(n)+f(n)) in O(f) 
  {
    assert f in O(f) 
      by { lem_Refl(f); }
    assert (n => f(n)+f(n)) == (n => 2.0*f(n))
      by { lem_Exten(n => f(n)+f(n), n => 2.0*f(n)); }
    assert (n => 2.0*f(n)) in O(f) 
      by { lem_Scale(f, f, 2.0); }
  }  

  // Power of two
  // f*f ∈ O(f^2)
  lemma lem_Pow2(f:nat->R0)  
    ensures (n => f(n)*f(n)) in O(n => ExpR.exp(f(n), 2.0)) 
  {
    assert (n => f(n)*f(n)) in O(n => f(n)*f(n)) 
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
  // f ∈ O(g) ∧ a > 0 ⟹ a*f ∈ O(g)
  lemma lem_Scale(f:nat->R0, g:nat->R0, a:R0)
    requires f in O(g) 
    requires a > 0.0 
    ensures  (n => a*f(n)) in O(g) 
  {  
    var c:R0, n0:nat :| c > 0.0 && bigOhFrom(c, n0, f, g);  
    assert forall n:nat :: 0 <= n0 <= n ==> f(n) <= c*g(n);
    
    // we show that c'=a*c and n0'=n0
    assert forall n:nat :: 0 <= n0 <= n ==> a*f(n) <= (a*c)*g(n);
    assert bigOhFrom(a*c, n0, n => a*f(n), g);
  }

  // Closure under addition
  // f1 ∈ O(g1) ∧ f2 ∈ O(g2) ⟹ f1+f2 ∈ O(g1+g2)
  lemma lem_Sum(f1:nat->R0, g1:nat->R0, f2:nat->R0, g2:nat->R0)  
    requires f1 in O(g1) 
    requires f2 in O(g2) 
    ensures  (n => f1(n)+f2(n)) in O(n => g1(n)+g2(n)) 
  {  
    var c1:R0, n1:nat :| c1 > 0.0 && bigOhFrom(c1, n1, f1, g1);  
    assert H1: forall n:nat :: 0 <= n1 <= n ==> f1(n) <= c1*g1(n);
    var c2:R0, n2:nat :| c2 > 0.0 && bigOhFrom(c2, n2, f2, g2);  
    assert H2: forall n:nat :: 0 <= n2 <= n ==> f2(n) <= c2*g2(n);   
    
    // we show that c=c1+c2 and n0=n1+n2 (not tight but works)
    var c:R0, n0:nat := c1+c2, n1+n2;
    forall n:nat | 0 <= n0 <= n
      ensures f1(n) + f2(n) <= c*(g1(n) + g2(n))
    {
      calc {
           f1(n) + f2(n); 
        <= { reveal H1, H2; }
           c1*g1(n) + c2*g2(n); 
        <= { assert c1 <= c1+c2; assert c2 <= c1+c2; }
           (c1+c2)*g1(n) + (c1+c2)*g2(n);
        == (c1+c2)*(g1(n) + g2(n)); 
        == c*(g1(n) + g2(n));         
      }
    }    
    assert bigOhFrom(c, n0, n => f1(n)+f2(n), n => g1(n)+g2(n));
  }

  // Closure under addition within the same class
  // f1 ∈ O(g) ∧ f2 ∈ O(g) ⟹ f1 + f2 ∈ O(g)
  lemma lem_SumSameClass(f1:nat->R0, f2:nat->R0, g:nat->R0)  
    requires f1 in O(g) 
    requires f2 in O(g) 
    ensures  (n => f1(n)+f2(n)) in O(g) 
  {  
    lem_Sum(f1, g, f2, g);  
    assert (n => f1(n)+f2(n)) in O(n => g(n)+g(n));
    assert (n => g(n)+g(n))   in O(g) by { lem_SumIdemp(g); }
    lem_Trans(n => f1(n)+f2(n), n => g(n)+g(n), g);
  }

  // Closure under multiplication
  // f1 ∈ O(g1) ∧ f2 ∈ O(g2) ⟹ f1*f2 ∈ O(g1*g2)
  lemma lem_Mul(f1:nat->R0, g1:nat->R0, f2:nat->R0, g2:nat->R0)  
    requires f1 in O(g1) 
    requires f2 in O(g2) 
    ensures  (n => f1(n)*f2(n)) in O(n => g1(n)*g2(n))  
  {  
    var c1:R0, n1:nat :| c1 > 0.0 && bigOhFrom(c1, n1, f1, g1);  
    assert H1: forall n:nat :: 0 <= n1 <= n ==> f1(n) <= c1*g1(n);
    var c2:R0, n2:nat :| c2 > 0.0 && bigOhFrom(c2, n2, f2, g2);  
    assert H2: forall n:nat :: 0 <= n2 <= n ==> f2(n) <= c2*g2(n);   
    
    // we show that c=c1*c2 and n0=n1+n2 (not tight but works)
    var c:R0, n0:nat := c1*c2, n1+n2;
    forall n:nat | 0 <= n0 <= n
      ensures f1(n) * f2(n) <= c*(g1(n) * g2(n))
    {
      calc {
           f1(n) * f2(n); 
        <= { reveal H1, H2; }
           c1*g1(n) * c2*g2(n); 
        == (c1*c2)*(g1(n) * g2(n));
        == c*(g1(n) * g2(n));         
      }
    }  
    assert bigOhFrom(c, n0, n => f1(n)*f2(n), n => g1(n)*g2(n));
  }

  // f ∈ O(g) ⟹ f+g ∈ O(g)
  lemma lem_SumSimpl(f:nat->R0, g:nat->R0)  
    requires f in O(g) 
    ensures  (n => f(n)+g(n)) in O(g)  
  {
    var c:R0, n0:nat :| c > 0.0 && bigOhFrom(c, n0, f, g);  
    assert H1: forall n:nat :: 0 <= n0 <= n ==> f(n) <= c*g(n);

    // prove f+g ∈ O(g)
    var c1:R0, n1:nat := c + 1.0, n0;
    forall n:nat | 0 <= n1 <= n
      ensures f(n) + g(n) <= c1*g(n)
    {
      calc {
           f(n) + g(n); 
        <= { reveal H1; }
           c*g(n) + g(n); 
        == (c + 1.0)*g(n);
        == c1*g(n);         
      }
    }  
    assert c1 > 0.0 && bigOhFrom(c1, n1, n => f(n)+g(n), g);
  }

  // f ∈ O(g) ⟹ g ∈ O(f+g)
  lemma lem_SumSynth(f:nat->R0, g:nat->R0)  
    requires f in O(g) 
    ensures  g in O(n => f(n)+g(n))  
  {
    var c1:R0, n1:nat := 1.0, 0;
    forall n:nat | 0 <= n1 <= n
      ensures g(n) <= c1*(f(n) + g(n))
    {
      calc {
           g(n);       
        <= f(n) + g(n);
        <= c1*(f(n) + g(n));
      }
    }  
    assert c1 > 0.0 && bigOhFrom(c1, n1, g, n => f(n)+g(n));
  }  

  // f ∈ O(g+h) ∧ g ∈ O(h) ⟹ f ∈ O(h)
  lemma lem_SumSimpl2(f:nat->R0, g:nat->R0, h:nat->R0)  
    requires f in O(n => g(n)+h(n)) 
    requires g in O(h) 
    ensures  f in O(h) 
  {
    lem_SumSimpl(g, h);
    assert (n => g(n)+h(n)) in O(h);
    lem_Trans(f, n => g(n)+h(n), h);
  }

  // Downward closure wrto <=
  // f(n) <= up(n) eventually ∧ up ∈ O(h) ⟹ f ∈ O(h)
  lemma lem_LEQdownwardClosure(f:nat->R0, up:nat->R0, h:nat->R0, n1:nat)  
    requires forall n:nat :: n >= n1 ==> f(n) <= up(n)
    requires up in O(h)
    ensures  f  in O(h)
  {  
    var c2:R0, n2:nat :| c2 > 0.0 && bigOhFrom(c2, n2, up, h);  
    assert H1: forall n:nat :: 0 <= n2 <= n ==> up(n) <= c2*h(n);

    var c:R0, n0:nat := c2, max(n1, n2);
    forall n:nat | 0 <= n0 <= n
      ensures f(n) <= c*h(n)
    {
      calc {
           f(n); 
        <= up(n);
        <= c2*h(n);         
      }
      assert f(n) <= c2*h(n);
    }
    assert c > 0.0 && bigOhFrom(c, n0, f, h);
  }

  /******************************************************************************
    Monotonicity properties
  ******************************************************************************/

  // f ∈ O(g) ⟹ O(f) ⊆ O(g)
  lemma lem_MonoIncr(f:nat->R0, g:nat->R0)  
    requires f in O(g)
    ensures  O(f) <= O(g) 
  {
    forall h:nat->R0 | h in O(f) 
      ensures h in O(g) 
    {
      calc {
            h in O(f);
        ==> { assert f in O(g); 
              lem_Trans(h, f, g); }
            h in O(g);
      }
    } 
  }

  /******************************************************************************
    Closure properties from the set-theoretic view
  ******************************************************************************/
  
  // Each result follows from it's corresponding membership version property

  // lem_Scale lifted to sets
  // f ∈ O(g) ∧ a > 0 ⟹ O(a*f) ⊆ O(g)
  lemma lem_ScaleSet(f:nat->R0, g:nat->R0, a:R0)
    requires f in O(g) 
    requires a > 0.0 
    ensures  O(n => a*f(n)) <= O(g) 
  {  
    assert (n => a*f(n)) in O(g) 
      by { lem_Scale(f, g, a); }    
    lem_MonoIncr(n => a*f(n), g);
  }

  // lem_Sum lifted to sets
  // f1 ∈ O(g1) ∧ f2 ∈ O(g2) ==> O(f1+f2) ⊆ O(g1+g2)
  lemma lem_SumSet(f1:nat->R0, g1:nat->R0, f2:nat->R0, g2:nat->R0) 
    requires f1 in O(g1) 
    requires f2 in O(g2) 
    ensures  O(n => f1(n)+f2(n)) <= O(n => g1(n)+g2(n)) 
  {  
    assert (n => f1(n)+f2(n)) in O(n => g1(n)+g2(n)) 
      by { lem_Sum(f1, g1, f2, g2); }    
    lem_MonoIncr(n => f1(n)+f2(n), n => g1(n)+g2(n));
  }  

  // lem_SumSameClass lifted
  // f1 ∈ O(g) ∧ f2 ∈ O(g) ⟹ O(f1+f2) ⊆ O(g)
  lemma lem_SumSameClassSet(f1:nat->R0, f2:nat->R0, g:nat->R0)  
    requires f1 in O(g) 
    requires f2 in O(g) 
    ensures  O(n => f1(n)+f2(n)) <= O(g) 
  {  
    assert (n => f1(n)+f2(n)) in O(g) 
      by { lem_SumSameClass(f1, f2, g); }    
    lem_MonoIncr(n => f1(n)+f2(n), g);
  }  

  // lem_Mul lifted to sets
  // f1 ∈ O(g1) ∧ f2 ∈ O(g2) ==> O(f1*f2) ⊆ O(g1*g2)
  lemma lem_MulSet(f1:nat->R0, g1:nat->R0, f2:nat->R0, g2:nat->R0)  
    requires f1 in O(g1)
    requires f2 in O(g2)
    ensures  O(n => f1(n)*f2(n)) <= O(n => g1(n)*g2(n)) 
  {  
    assert (n => f1(n)*f2(n)) in O(n => g1(n)*g2(n)) 
      by { lem_Mul(f1, g1, f2, g2);  }
    lem_MonoIncr(n => f1(n)*f2(n), n => g1(n)*g2(n));
  }   

  // f ∈ O(g) ⟹ O(f+g) = O(g)
  lemma lem_SumSimplSet(f:nat->R0, g:nat->R0)  
    requires f in O(g) 
    ensures  O(n => f(n)+g(n)) == O(g)
  {
    // prove O(f+g) ⊆ O(g)
    assert (n => f(n)+g(n)) in O(g) 
      by { lem_SumSimpl(f, g); }    
    lem_MonoIncr(n => f(n)+g(n), g);

    // prove O(g) ⊆ O(f+g)
    assert g in O(n => f(n)+g(n))
      by { lem_SumSynth(f, g); }  
    lem_MonoIncr(g, n => f(n)+g(n));
  }

  /******************************************************************************
    Equivalence properties (on classes)
  ******************************************************************************/

  // O(f) = O(g) induces an equivalence relation on functions

  // Equivalence of representatives
  // O(f) = O(g) ⟹ f ∈ O(g) ∧ g ∈ O(f)
  lemma lem_EqRepr(f:nat->R0, g:nat->R0)  
    requires O(f) == O(g)
    ensures  f in O(g) && g in O(f)
  { 
    assert f in O(f) by { lem_Refl(f); }
    assert g in O(g) by { lem_Refl(g); }
  }

  /******************************************************************************
    Congruence properties
  ******************************************************************************/

  // These show that equivalence is preserved under operations or relations

  // Congruence of membership
  // O(f) = O(g) ∧ f ∈ O(h) ⟹ g ∈ O(h)
  lemma lem_CongMember(f:nat->R0, g:nat->R0, h:nat->R0)  
    requires O(f) == O(g)
    requires f in O(h)
    ensures  g in O(h) 
  {
    lem_EqRepr(f, g);
    assert g in O(f);
    assert f in O(h);
    lem_Trans(g, f, h);
  }

  // Congruence of order
  // O(f) = O(g) ∧ O(h) = O(k) ∧ f ∈ O(h) ⟹ g ∈ O(k)
  lemma lem_CongOrder(f:nat->R0, g:nat->R0, h:nat->R0, k:nat->R0)  
    requires O(f) == O(g)
    requires O(h) == O(k)
    requires f in O(h)
    ensures  g in O(k)  
    // TODO

  /******************************************************************************
    Zero functions and the class O(0)
  ******************************************************************************/

  // Any function eventually zero is O(0)
  lemma lem_EventuallyZeroGrowth(f:nat->R0, n0:nat)  
    requires EventuallyZero(f, n0)
    ensures  f in O(zeroGrowth())
  {  
    var c:R0, n0:nat := 1.0, n0;
    forall n:nat | 0 <= n0 <= n
      ensures f(n) <= c*zeroGrowth()(n)
    {
      calc {
           f(n); 
        == 0.0;
        <= c*0.0;      
        == c*zeroGrowth()(n);         
      }
    }
    assert c > 0.0 && bigOhFrom(c, n0, f, zeroGrowth());
  }

  // Reverse direction of lem_EventuallyZeroGrowth
  // Any function in O(0) is eventually zero
  lemma lem_EventuallyZeroGrowthREV(f:nat->R0)  
    requires f in O(zeroGrowth()) 
    ensures  exists n0 :: EventuallyZero(f, n0)
  {  
    var c:R0, n1:nat :| c > 0.0 && bigOhFrom(c, n1, f, zeroGrowth());  
    assert H1: forall n:nat :: 0 <= n1 <= n ==> f(n) <= c*zeroGrowth()(n);

    forall n:nat | n1 <= n ensures f(n) == 0.0 { }
    assert EventuallyZero(f, n1);
    assert exists n0 :: EventuallyZero(f, n0);
  }  

  // Join previous facts into an equivalence
  // This serves as a characterization of the O(0) class
  // f in O(0) ⟺ f eventually zero
  lemma lem_EventuallyZeroGrowthIFF(f:nat->R0)  
    ensures f in O(zeroGrowth()) <==> exists n0 :: EventuallyZero(f, n0)
  {  
    assert f in O(zeroGrowth()) ==> exists n0 :: EventuallyZero(f, n0) by {
      if f in O(zeroGrowth()) {
        lem_EventuallyZeroGrowthREV(f); 
      }
    }
    assert (exists n0 :: EventuallyZero(f, n0)) ==> f in O(zeroGrowth()) by {
      if exists n0 :: EventuallyZero(f, n0) {
        var n0 :| EventuallyZero(f, n0);
        lem_EventuallyZeroGrowth(f, n0);
      }
    }    
  }  

  // Zero function is O(0)
  lemma lem_ZeroGrowth(f:nat->R0)  
    requires AlwaysZero(f)
    ensures  f in O(zeroGrowth())
  {  
    lem_EventuallyZeroGrowth(f, 0); 
  }

  /******************************************************************************
    Const functions and the class O(1)
  ******************************************************************************/

  // Any function eventually const is O(1)
  // Note: the reverse doesn't hold
  lemma lem_EventuallyConstGrowth(f:nat->R0, a:R0, n0:nat)  
    requires EventuallyConst(f, a, n0)
    ensures  f in O(constGrowth())
  {  
    var c:R0, n0:nat := a+1.0, n0;
    forall n:nat | 0 <= n0 <= n
      ensures f(n) <= c*constGrowth()(n)
    {
      calc {
           f(n); 
        == a;
        <= (a+1.0)*1.0;      
        == c*constGrowth()(n);         
      }
    }
    assert c > 0.0 && bigOhFrom(c, n0, f, constGrowth());
  }  

  // Any const function is O(1)
  lemma lem_ConstGrowth(f:nat->R0, a:R0)  
    requires AlwaysConst(f, a)
    ensures  f in O(constGrowth())
  {  
    lem_EventuallyConstGrowth(f, a, 0);
  }

  // Any function eventually bounded above by a const is O(1)
  lemma lem_EventuallyBoundConstGrowth(f:nat->R0, a:R0, n0:nat)  
    requires EventuallyConstBoundAbove(f, a, n0)
    ensures  f in O(constGrowth())
  {  
    var c:R0, n0:nat := a+1.0, n0;
    forall n:nat | 0 <= n0 <= n
      ensures f(n) <= c*constGrowth()(n)
    {
      calc {
           f(n); 
        <= a;
        <= (a+1.0)*1.0;      
        == c*constGrowth()(n);         
      }
    }
    assert c > 0.0 && bigOhFrom(c, n0, f, constGrowth());
  }

  // Reverse direction of lem_EventuallyBoundConstGrowth
  // Any function in O(1) is eventually bounded above by a const
  lemma lem_EventuallyBoundConstGrowthREV(f:nat->R0)  
    requires f in O(constGrowth())  
    ensures  exists a, n0 :: EventuallyConstBoundAbove(f, a, n0)
  {  
    var c:R0, n1:nat :| c > 0.0 && bigOhFrom(c, n1, f, constGrowth());  
    assert H1: forall n:nat :: 0 <= n1 <= n ==> f(n) <= c*constGrowth()(n);

    forall n:nat | n1 <= n ensures f(n) <= c { }
    assert EventuallyConstBoundAbove(f, c, n1);
    assert exists a, n0 :: EventuallyConstBoundAbove(f, a, n0);   
  }  

  // Join previous facts into an equivalence
  // This serves as a characterization of the O(1) class
  // f in O(1) ⟺ f eventually bounded above by a const
  lemma lem_EventuallyBoundConstGrowthIFF(f:nat->R0)  
    ensures f in O(constGrowth()) <==> exists n0, a :: EventuallyConstBoundAbove(f, a, n0)
  {  
    assert f in O(constGrowth()) ==> exists n0, a :: EventuallyConstBoundAbove(f, a, n0) by {
      if f in O(constGrowth()) {
        lem_EventuallyBoundConstGrowthREV(f); 
      }
    }
    assert (exists a, n0 :: EventuallyConstBoundAbove(f, a, n0)) ==> f in O(constGrowth()) by {
      if exists a, n0 :: EventuallyConstBoundAbove(f, a, n0) {
        var a, n0 :| EventuallyConstBoundAbove(f, a, n0);
        lem_EventuallyBoundConstGrowth(f, a, n0);
      }
    }     
  }  

  /******************************************************************************
    Logarithms and the class O(log_b)
  ******************************************************************************/

  // The base of log doesn't change asymptotics
  // b1,b2 > 0 ⟹ (h ∈ O(log_b1) ⟺ h ∈ O(log_b2))
  lemma lem_LogBase(b1:real, b2:real, h:nat->R0)  
    requires b1 > 1.0 && b2 > 1.0
    requires h in O(logGrowth(b1))
    ensures  h in O(logGrowth(b2))
  {
    var c1:R0, n0:nat :| c1 > 0.0 && bigOhFrom(c1, n0, h, logGrowth(b1));
    assert H1: forall n:nat :: 0 <= n0 <= n ==> h(n) <= c1*logGrowth(b1)(n); 

    LogR.lem_NonNegative(b2, b1);
    var G:R0 := LogR.log(b2, b1); 
    assert G > 0.0 by { LogR.lem_Positive(b2, b1); }
    var c1':R0, n0':nat := c1/G, n0+1;
    forall n:nat | 0 <= n0' <= n
      ensures h(n) <= c1'*logGrowth(b2)(n)
    {
      calc {
           h(n);
        <= { reveal H1; }
           c1*(LogR.log(b1, n as R0));
        == { LogR.lem_ChangeOfBase(b1, b2, n as R0); }
           c1*(LogR.log(b2, n as R0)/G);  
        == c1'*LogR.log(b2, n as R0);   
        == c1'*logGrowth(b2)(n);      
      }
    }
    assert c1' > 0.0 && bigOhFrom(c1', n0', h, logGrowth(b2));
  } 

  // b1,b2 > 0 ⟹ O(log_b1) = O(log_b2)
  lemma lem_LogBaseSet(b1:real, b2:real)  
    requires b1 > 1.0 && b2 > 1.0
    ensures  O(logGrowth(b1)) == O(logGrowth(b2))
  {
    forall h:nat->R0
      ensures h in O(logGrowth(b1)) <==> h in O(logGrowth(b2))
    {
      assert h in O(logGrowth(b1)) ==> h in O(logGrowth(b2)) by { 
        if h in O(logGrowth(b1)) {
          lem_LogBase(b1, b2, h); 
        }
      }
      assert h in O(logGrowth(b2)) ==> h in O(logGrowth(b1)) by { 
        if h in O(logGrowth(b2)) {
          lem_LogBase(b2, b1, h); 
        }
      }      
    }
  }

  /******************************************************************************
    Membership between common growth rates
  ******************************************************************************/

  // 0 ∈ O(f) 
  lemma lem_ZeroInAny(f:nat->R0)
    ensures zeroGrowth() in O(f) 
  {
    var c:R0, n0:nat := 1.0, 0;
    forall n:nat | 0 <= n0 <= n 
      ensures zeroGrowth()(n) <= c*f(n)
    {
      calc {
           zeroGrowth()(n);
        == 0.0;
        <= 1.0*f(n);             
      }
    }
    assert c > 0.0 && bigOhFrom(c, n0, zeroGrowth(), f);
  } 

  // 0 ∈ O(1) 
  lemma lem_ZeroInConst()
    ensures zeroGrowth() in O(constGrowth()) 
  {
    lem_ZeroInAny(constGrowth());
  }   

  // 1 ∈ O(log_b) 
  lemma lem_ConstInLog(b:R0)
    requires b > 1.0
    ensures  constGrowth() in O(logGrowth(b))
  {
    var c:R0, n0:nat := 1.0, ceil(b);
    forall n:nat | 0 <= n0 <= n 
      ensures constGrowth()(n) <= c*logGrowth(b)(n)
    {
      calc {
           constGrowth()(n);
        == 1.0;
        <= { LogR.lem_GEQone(b, n as R0); }
           1.0*logGrowth(b)(n);
        == c*logGrowth(b)(n);         
      }
    }
    assert bigOhFrom(c, n0, constGrowth(), logGrowth(b));
  } 

  // 1 ∈ O(log2) 
  lemma lem_ConstInLog2()
    ensures constGrowth() in O(log2Growth()) 
  {
    lem_ConstInLog(2.0);
    assert constGrowth() in O(logGrowth(2.0));
    lem_Exten(log2Growth(), logGrowth(2.0)) 
      by { reveal Log2R.log2(); }
  }    

  // 1 ∈ O(n) 
  lemma lem_ConstInLin()
    ensures constGrowth() in O(linGrowth()) 
  {
    // From transitivity of 1 ∈ O(log2) and log2 ∈ O(n)  
    assert constGrowth() in O(log2Growth()) by { lem_ConstInLog2(); }
    assert log2Growth()  in O(linGrowth())  by { lem_Log2InLin(); }
    lem_Trans(constGrowth(), log2Growth(), linGrowth());
  }    

  // k >= 1 ⟹ 1 ∈ O(n^k)  
  lemma lem_ConstInPoly(k:R0)
    requires k >= 1.0
    ensures  constGrowth() in O(polyGrowth(k)) 
  {
    // From transitivity of 1 ∈ O(log2) and log2 ∈ O(n^k)  
    assert constGrowth() in O(log2Growth())  by { lem_ConstInLog2(); }
    assert log2Growth()  in O(polyGrowth(k)) by { lem_Log2InPoly(k); }
    lem_Trans(constGrowth(), log2Growth(), polyGrowth(k));
  } 

  // b >= 2 ⟹ 1 ∈ O(b^n)  
  lemma lem_ConstInExp(b:R0)
    requires b >= 2.0
    ensures  constGrowth() in O(expGrowth(b)) 
  {
    // From transitivity of 1 ∈ O(n) and n ∈ O(b^n)  
    assert constGrowth() in O(linGrowth())  by { lem_ConstInLin(); }
    assert linGrowth()   in O(expGrowth(b)) by { lem_LinInExp(b); }
    lem_Trans(constGrowth(), linGrowth(), expGrowth(b));
  }   

  // log2 ∈ O(n) 
  lemma lem_Log2InLin()
    ensures log2Growth() in O(linGrowth()) 
  {
    var c:R0, n0:nat := 1.0, 1;
    forall n:nat | 0 <= n0 <= n
      ensures log2Growth()(n) <= c*linGrowth()(n)
    {
      calc {      
           log2Growth()(n); 
        == Log2R.log2(n as real);
        <  { Log2R.lem_NatUpBound(n); }
           (Log2N.log2(n) + 1) as R0;
        <= { lem_log2nLEQnMinus1(n); }
           ((n - 1) + 1) as R0;   
        == n as R0;   
        <= c*n as R0;
        == c*linGrowth()(n);
      }
    }
    assert bigOhFrom(c, n0, log2Growth(), linGrowth());
  }

  // log_b ∈ O(n) 
  lemma lem_LogInLin(b:R0)
    requires b > 1.0
    ensures logGrowth(b) in O(linGrowth()) 
  {  
    lem_LogBaseSet(2.0, b);  
    lem_Log2InLin();   
    lem_Exten(log2Growth(), logGrowth(2.0)) by { reveal Log2R.log2(); }

    lem_CongMember(logGrowth(2.0), logGrowth(b), linGrowth());
  }

  // log2(n+1) ∈ O(n) 
  lemma lem_Log2Plus1InLin()
    ensures log2Plus1Growth() in O(linGrowth())
  {
    var c:R0, n0:nat := 2.0, 1;
    forall n:nat | 0 <= n0 <= n
      ensures log2Plus1Growth()(n) <= c*linGrowth()(n)
    {
      calc {      
           log2Plus1Growth()(n); 
        == Log2R.log2((n+1) as real);
        <  { Log2R.lem_NatUpBound(n+1);  }
           (Log2N.log2(n+1) + 1) as R0;
        <= { lem_log2nPlus1LEQn(n); }
           (n + 1) as R0;   
        <= c*n as R0;
        == c*linGrowth()(n);
      }
    }
    assert bigOhFrom(c, n0, log2Plus1Growth(), linGrowth());    
  }

  // k >= 1 ⟹ log2 ∈ O(n^k) 
  lemma lem_Log2InPoly(k:R0)
    requires k >= 1.0
    ensures  log2Growth() in O(polyGrowth(k))
  { 
    // From transitivity of log2 ∈ O(n) and n ∈ O(n^k)  
    assert log2Growth() in O(linGrowth())   by { lem_Log2InLin(); }
    assert linGrowth()  in O(polyGrowth(k)) by { lem_LinInPoly(k); }
    lem_Trans(log2Growth(), linGrowth(), polyGrowth(k));    
  }

  // b > 1 ∧ k >= 1 ⟹ log_b ∈ O(n^k) 
  lemma lem_LogInPoly(b:R0, k:R0)
    requires b > 1.0 && k >= 1.0
    ensures logGrowth(b) in O(polyGrowth(k))
  {  
    // From transitivity of log_b ∈ O(n) and n ∈ O(n^k)  
    assert logGrowth(b) in O(linGrowth())   by { lem_LogInLin(b); }
    assert linGrowth()  in O(polyGrowth(k)) by { lem_LinInPoly(k); }
    lem_Trans(logGrowth(b), linGrowth(), polyGrowth(k));    
  }  

  // k >= 1 ⟹ n ∈ O(n^k) 
  lemma lem_LinInPoly(k:R0)
    requires k >= 1.0
    ensures  linGrowth() in O(polyGrowth(k)) 
  { 
    var c:R0, n0:nat := 1.0, 1;
    forall n:nat | 0 <= n0 <= n
      ensures linGrowth()(n) <= c*polyGrowth(k)(n)
    {
      calc {      
           linGrowth()(n); 
        == n as R0;  
        == { ExpR.lem_Pow1(n as R0); }
           ExpR.exp(n as R0, 1.0);
        <= { ExpR.lem_MonoIncr(n as R0, 1.0, k); }
           ExpR.exp(n as R0, k);
        <= c*ExpR.exp(n as R0, k);
        == c*polyGrowth(k)(n);
      }
    }
    assert bigOhFrom(c, n0, linGrowth(), polyGrowth(k));
  }

  // n ∈ O(n^2) 
  lemma lem_LinInQuad()
    ensures linGrowth() in O(quadGrowth()) 
  {
    lem_LinInPoly(2.0);
    ExpR.lem_Pow2Auto();
    lem_Exten((n:nat) => ExpR.exp(n as R0, 2.0), (n:nat) => (n*n) as R0);
  }

  // n ∈ O(n^3) 
  lemma lem_LinInCubic()
    ensures linGrowth() in O(cubicGrowth()) 
  { 
    lem_LinInPoly(3.0);
    ExpR.lem_Pow3Auto();
    lem_Exten((n:nat) => ExpR.exp(n as R0, 3.0), (n:nat) => (n*n*n) as R0);    
  }  

  // n^2 ∈ O(2^n)  
  lemma lem_QuadInExp()
    ensures quadGrowth() in O(exp2Growth()) 
  {
    var c:R0, n0:nat := 1.0, 4;
    forall n:nat | 0 <= n0 <= n
      ensures quadGrowth()(n) <= c*exp2Growth()(n)
    {
      calc {      
           quadGrowth()(n); 
        == (n*n) as R0;
        == { ExpR.lem_Pow2(n as R0); }
           ExpR.exp(n as R0, 2.0);          
        == { ExpR.lem_EqExpNat(n, 2); }
           ExpN.exp(n, 2) as real;
        <= { lem_expn2LEQexp2n(n); }  
           ExpN.exp(2, n) as real; 
        == { ExpR.lem_EqExpNat(2, n); }     
           ExpR.exp(2.0, n as R0); 
        <= c*ExpR.exp(2.0, n as R0);
        == c*ExpR.exp2(n as R0);
        == c*exp2Growth()(n);
      }
    }
    assert bigOhFrom(c, n0, quadGrowth(), exp2Growth());
  }

  // n ∈ O(2^n)  
  lemma lem_LinInExp2()
    ensures linGrowth() in O(exp2Growth()) 
  {
    // From transitivity of n ∈ O(n^2) and n^2 ∈ O(2^n)  
    assert linGrowth()  in O(quadGrowth()) by { lem_LinInQuad(); }
    assert quadGrowth() in O(exp2Growth()) by { lem_QuadInExp(); }
    lem_Trans(linGrowth(), quadGrowth(), exp2Growth());
  }

  // n ∈ O(b^n)  
  lemma lem_LinInExp(b:R0)
    requires b >= 2.0
    ensures  linGrowth() in O(expGrowth(b)) 
  { 
    // From transitivity of n ∈ O(2^n) and 2^n ∈ O(b^n)  
    assert linGrowth()  in O(exp2Growth()) by { lem_LinInExp2(); }
    assert exp2Growth() in O(expGrowth(b)) by { lem_Exp2InExp(b); }
    lem_Trans(linGrowth(), exp2Growth(), expGrowth(b));
  }    

  // k >= 0 ⟹ n^k ∈ O(2^n)  
  lemma lem_PolyInExp2(k:R0)
    requires k >= 0.0
    ensures  polyGrowth(k) in O(exp2Growth())
  // TODO

  // b >= 2 ⟹ 2^n ∈ O(b^n)  
  lemma lem_Exp2InExp(b:R0)
    requires b >= 2.0
    ensures  exp2Growth() in O(expGrowth(b))
  {
    var c:R0, n0:nat := 1.0, 1;
    forall n:nat | 0 <= n0 <= n
      ensures exp2Growth()(n) <= c*expGrowth(b)(n)
    {
      calc {      
           exp2Growth()(n); 
        == ExpR.exp2(n as R0);        
        == ExpR.exp(2.0, n as R0);
        <= { ExpR.lem_BaseMonoIncr(n as R0, 2.0, b); }
           ExpR.exp(b, n as R0);
        <= c*ExpR.exp(b, n as R0);
        == c*expGrowth(b)(n);
      }
    }
    assert bigOhFrom(c, n0, exp2Growth(), expGrowth(b));    
  }

  // k >= 0 ∧ b >= 2 ⟹ n^k ∈ O(b^n)  
  lemma lem_PolyInExp(k:R0, b:R0)
    requires k >= 0.0 && b >= 2.0
    ensures  polyGrowth(k) in O(expGrowth(b))
  {
    // From transitivity of n^k ∈ O(2^n) and 2^n ∈ O(b^n)  
    assert polyGrowth(k) in O(exp2Growth()) by { lem_PolyInExp2(k); }
    assert exp2Growth()  in O(expGrowth(b)) by { lem_Exp2InExp(b); }
    lem_Trans(polyGrowth(k), exp2Growth(), expGrowth(b));
  }

  /******************************************************************************
    Non-membership between common growth rates
  ******************************************************************************/

  // Any non-zero const function is not O(0)
  lemma lem_ConstNotInZero(f:nat->R0, a:R0)  
    requires a > 0.0 
    requires forall n:nat :: f(n) == a
    ensures  f !in O(zeroGrowth())
  {  
    assert forall c:R0, n0:nat :: c > 0.0 ==> !bigOhFrom(c, n0, f, zeroGrowth()) by {
      forall c:R0, n0:nat | c > 0.0
        ensures !bigOhFrom(c, n0, f, zeroGrowth())
      {
        var n :| 0 <= n0 <= n;
        assert f(n) > c*zeroGrowth()(n);

        calc {
             f(n); 
          == a;
          > 0.0;      
          == c*zeroGrowth()(n);         
        }
      }
    }
    assert !bigOh(f, zeroGrowth());
  }

  /******************************************************************************
    Inclusion hierarchy: bigger growth functions contain smaller-growth functions.
    Reverse of Ω inclusion hierarchy.

      O(0) ⊆ O(1) ⊆ O(log_b)
                  ⊆ O(n^1) ⊆ O(n^2) ⊆ ... ⊆ O(n^k) 
                  ⊆ O(2^n) ⊆ O(3^n) ⊆ ... ⊆ O(b^n) 

    Proving O(f) ⊆ O(g) amounts to proving f ∈ O(g) and using transitivity, which
    is exactly what lem_MonoIncr give us.               
  ******************************************************************************/

  // O(0) ⊆ O(1) 
  lemma lem_ZeroLeqConst()
    ensures O(zeroGrowth()) <= O(constGrowth()) 
  {
    lem_ZeroInConst();
    lem_MonoIncr(zeroGrowth(), constGrowth());
  }

  // O(1) ⊆ O(log_b) 
  lemma lem_ConstLeqLog(b:R0)
    requires b > 1.0
    ensures O(constGrowth()) <= O(logGrowth(b)) 
  {
    lem_ConstInLog(b);
    lem_MonoIncr(constGrowth(), logGrowth(b));
  }  

  // O(log_b) ⊆ O(n^k) 
  lemma lem_LogLeqPoly(b:R0, k:R0)
    requires b > 1.0 && k >= 1.0
    ensures O(logGrowth(b)) <= O(polyGrowth(k)) 
  {
    lem_LogInPoly(b, k); 
    lem_MonoIncr(logGrowth(b), polyGrowth(k));
  }  

  // O(n^k) ⊆ O(b^n) 
  lemma lem_PolyLeqExp(k:R0, b:R0)
    requires k >= 0.0 && b >= 2.0
    ensures O(polyGrowth(k)) <= O(expGrowth(b)) 
  {
    lem_PolyInExp(k, b); 
    lem_MonoIncr(polyGrowth(k), expGrowth(b));
  }  

  /******************************************************************************
    Proper inclusion hierarchy

      O(0) ⊂ O(1) ⊂ O(log_b)
                  ⊂ O(n^2) ⊂ O(n^3) ⊂ ... ⊂ O(n^k) 
                  ⊂ O(2^n) ⊂ O(3^n) ⊂ ... ⊂ O(b^n) 

    Proving O(f) ⊂ O(g) amounts to proving O(f) ⊆ O(g) and showing some h such 
    that h ∈ O(g) but h ∉ O(f).               
  ******************************************************************************/

  // O(0) ⊂ O(1) 
  lemma lem_ZeroLtConst()
    ensures O(zeroGrowth()) < O(constGrowth()) 
  {
    lem_ZeroLeqConst();

    // Let f be the always 1 function
    var f:nat->R0 :| forall n:nat :: f(n) == 1.0;

    lem_ConstGrowth(f, 1.0);     // f ∈ O(1)
    lem_ConstNotInZero(f, 1.0);  // f ∉ O(0)
  }

}