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
include "../math/Misc.dfy"
include "../math/TypeR0.dfy"
include "./Asymptotics.dfy"
include "./LemBigOh.dfy"
include "./LemBigOm.dfy"

/******************************************************************************
  Lemmas of Big Theta
******************************************************************************/

module LemBigTh {

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
  import opened Misc
  import opened TypeR0 
  import opened Asymptotics
  import LemOh = LemBigOh
  import LemOm = LemBigOm

  /******************************************************************************
    Order properties on functions
  ******************************************************************************/

  // Θ behaves like an equivalence relation (refl + sym + trans) on functions

  // Reflexivity
  // f ∈ Θ(f)
  lemma lem_Refl(f:nat->R0)  
    ensures f in Th(f) 
  {  
    LemOh.lem_Refl(f); 
    LemOm.lem_Refl(f);
    lem_Def2ImpDef(f, f);
  }  

  // Symmetry
  // f ∈ Θ(g) ⟹ g ∈ Θ(f)
  lemma lem_Sym(f:nat->R0, g:nat->R0)  
    requires f in Th(g) 
    ensures  g in Th(f)
  // TODO  

  // Transitivity
  // f ∈ Ω(g) ∧ g ∈ Ω(h) ⟹ f ∈ Ω(h)
  lemma lem_Trans(f:nat->R0, g:nat->R0, h:nat->R0)  
    requires f in Th(g) 
    requires g in Th(h)  
    ensures  f in Th(h)  
  {
    lem_DefImpDef2(f, g);
    lem_DefImpDef2(g, h);
    LemOh.lem_Trans(f, g, h); 
    LemOm.lem_Trans(f, g, h);
    lem_Def2ImpDef(f, h);
  }  

  /******************************************************************************
    Structural properties
  ******************************************************************************/

  // Idempotency under addition
  // f + f ∈ Θ(f)
  lemma lem_SumIdemp(f:nat->R0)  
    ensures (n => f(n)+f(n)) in Th(f) 
  {
    assert f in Th(f) 
      by { lem_Refl(f); }
    assert (n => f(n)+f(n)) == (n => 2.0*f(n))
      by { lem_Exten(n => f(n)+f(n), n => 2.0*f(n)); }
    assert (n => 2.0*f(n)) in Th(f) 
      by { lem_Scale(f, f, 2.0); }
  }  

  // Power of two
  // f*f ∈ Θ(f^2)
  lemma lem_Pow2(f:nat->R0)  
    ensures (n => f(n)*f(n)) in Th(n => ExpR.exp(f(n), 2.0)) 
  {
    assert (n => f(n)*f(n)) in Th(n => f(n)*f(n)) 
      by { lem_Refl(n => f(n)*f(n)); }
    assert (n => f(n)*f(n)) == (n => ExpR.exp(f(n), 2.0))
      by { ExpR.lem_Pow2Auto();
           lem_Exten(n => f(n)*f(n), n => ExpR.exp(f(n), 2.0)); }
  } 

  /******************************************************************************
    bigTh and bigTh2 are equivalent definitions of Θ 
  ******************************************************************************/

  lemma lem_DefEqDef2(f:nat->R0, g:nat->R0)  
    ensures bigTh(f, g) <==> bigTh2(f, g)
  {
    assert bigTh(f, g) ==> bigTh2(f, g) by {
      if bigTh(f, g) {
        lem_DefImpDef2(f, g);
      }      
    }
    assert bigTh2(f, g) ==> bigTh(f, g) by {
      if bigTh2(f, g) {
        lem_Def2ImpDef(f, g);
      }      
    }
  }

  lemma lem_DefImpDef2(f:nat->R0, g:nat->R0)  
    requires bigTh(f, g) 
    ensures  bigTh2(f, g)
  {
    var c1:R0, c2:R0, n0:nat :| c1 > 0.0 && c2 > 0.0 && bigThFrom(c1, c2, n0, f, g); 
    assert H: forall n:nat :: 0 <= n0 <= n ==> c1*g(n) <= f(n) <= c2*g(n);

    assert A: f in O(g) by {
      forall n:nat | 0 <= n0 <= n
        ensures f(n) <= c2*g(n)
      {
        assert f(n) <= c2*g(n) by { reveal H; }
      }
      assert bigOhFrom(c2, n0, f, g);
    }
    assert B: f in Om(g) by {
      forall n:nat | 0 <= n0 <= n
        ensures c1*g(n) <= f(n)
      {
        assert c1*g(n) <= f(n) by { reveal H; }
      }
      assert bigOmFrom(c1, n0, f, g);
    }
    
    assert f in O(g) && f in Om(g) by { reveal A, B; }
  }      

  lemma lem_Def2ImpDef(f:nat->R0, g:nat->R0)  
    requires bigTh2(f, g) 
    ensures  bigTh(f, g)
  {
    var c1:R0, n0_1:nat :| c1 > 0.0 && bigOmFrom(c1, n0_1, f, g) ; 
    assert H1: forall n:nat :: 0 <= n0_1 <= n ==> c1*g(n) <= f(n);

    var c2:R0, n0_2:nat :| c2 > 0.0 && bigOhFrom(c2, n0_2, f, g) ; 
    assert H2: forall n:nat :: 0 <= n0_2 <= n ==> f(n) <= c2*g(n);

    var n0 := n0_1 + n0_2;
    forall n:nat | 0 <= n0 <= n
      ensures c1*g(n) <= f(n) <= c2*g(n)
    {
      assert c1*g(n) <= f(n) by { reveal H1; }
      assert f(n) <= c2*g(n) by { reveal H2; }
    }
    assert bigThFrom(c1, c2, n0, f, g);
  }

  // A stronger way to conclude a program counter t is Θ(g) for input size n
  lemma lem_tIsBigTh2(n:nat, t:R0, g:nat->R0)  
    requires exists f:nat->R0 :: f(n) == t && bigTh(f, g)
    ensures  tIsBigTh(n, t, g) 
  {
    var f:nat->R0 :| f(n) == t && bigTh(f, g);
    lem_DefImpDef2(f, g);
  }

  /******************************************************************************
    Closure properties
  ******************************************************************************/

  // These describe how the classes behave under operations

  // Closure under scaling
  // f ∈ Θ(g) ∧ a > 0 ⟹ a*f ∈ Θ(g)
  lemma lem_Scale(f:nat->R0, g:nat->R0, a:R0)
    requires f in Th(g) 
    requires a > 0.0 
    ensures  (n => a*f(n)) in Th(g) 
  {  
    lem_DefImpDef2(f, g);
    LemOh.lem_Scale(f, g, a);
    LemOm.lem_Scale(f, g, a);
    lem_Def2ImpDef(n => a*f(n), g);
  }

  // Closure under addition
  // f1 ∈ Θ(g1) ∧ f2 ∈ Θ(g2) ⟹ f1+f2 ∈ Θ(g1+g2)
  lemma lem_Sum(f1:nat->R0, g1:nat->R0, f2:nat->R0, g2:nat->R0)  
    requires f1 in Th(g1) 
    requires f2 in Th(g2) 
    ensures  (n => f1(n)+f2(n)) in Th(n => g1(n)+g2(n)) 
  {  
    lem_DefImpDef2(f1, g1);
    lem_DefImpDef2(f2, g2);
    LemOh.lem_Sum(f1, g1, f2, g2);
    LemOm.lem_Sum(f1, g1, f2, g2);
    lem_Def2ImpDef(n => f1(n)+f2(n), n => g1(n)+g2(n));    
  }

  // Closure under addition within the same class
  // f1 ∈ Θ(g) ∧ f2 ∈ Θ(g) ⟹ f1 + f2 ∈ Θ(g)
  lemma lem_SumSameClass(f1:nat->R0, f2:nat->R0, g:nat->R0)  
    requires f1 in Th(g) 
    requires f2 in Th(g) 
    ensures  (n => f1(n)+f2(n)) in Th(g) 
  {  
    lem_Sum(f1, g, f2, g);  
    assert (n => f1(n)+f2(n)) in Th(n => g(n)+g(n));
    assert (n => g(n)+g(n))   in Th(g) by { lem_SumIdemp(g); }
    lem_Trans(n => f1(n)+f2(n), n => g(n)+g(n), g);
  }

  // f ∈ O(g) ⟹ f+g ∈ Θ(g)
  lemma lem_SumSimpl(f:nat->R0, g:nat->R0)  
    requires f in O(g) 
    ensures  (n => f(n)+g(n)) in Th(g)    
  {
    LemOh.lem_SumSimpl(f, g);
    LemOm.lem_SumSimpl(f, g);
    lem_Def2ImpDef(n => f(n)+g(n), g);
  }  

  // f ∈ O(g) ⟹ Θ(f+g) = Θ(g)
  lemma lem_SumSimplSet(f:nat->R0, g:nat->R0)  
    requires f in O(g) 
    ensures  Th(n => f(n)+g(n)) == Th(g) 
  {
    // prove Θ(f+g) ⊆ Θ(g)
    forall h:nat->R0 | h in Th(n => f(n)+g(n)) 
      ensures h in Th(g) 
    {
      assert h in Th(n => f(n)+g(n));  
      assert (n => f(n)+g(n)) in Th(g) 
        by { lem_SumSimpl(f, g); }
      lem_Trans(h, n => f(n)+g(n), g);  
    }    
    
    // prove Θ(g) ⊆ Θ(f+g)
    forall h:nat->R0 | h in Th(g)
      ensures h in Th(n => f(n)+g(n)) 
    {
      assert h in Th(g);  
      assert g in Th(n => f(n)+g(n))
        by { lem_SumSimpl(f, g); lem_Sym(n => f(n)+g(n), g); }
      lem_Trans(h, g, n => f(n)+g(n));   
    }  
  } 

  //   lo(n) <= f(n)  eventually ∧ lo ∈ Ω(h) 
  // ∧ f(n)  <= up(n) eventually ∧ up ∈ O(h)  
  // ⟹ f ∈ Θ(h)
  lemma lem_SandwichClosure(f:nat->R0, lo:nat->R0, up:nat->R0, g:nat->R0, n1:nat, n2:nat)  
    requires forall n:nat :: n >= n1 ==> lo(n) <= f(n)
    requires forall n:nat :: n >= n2 ==> f(n)  <= up(n)
    requires lo in Om(g)
    requires up in O(g)
    ensures  f  in Th(g)
  {
    assert f in Om(g) by {
      LemOm.lem_LEQupwardClosure(f, lo, g, n1);
    }
    assert f in O(g) by {
      LemOh.lem_LEQdownwardClosure(f, up, g, n2);
    }    
    assert f in Th(g) by {
      lem_DefEqDef2(f, g);
    }
  }

  /******************************************************************************
    Monotonicity properties
  ******************************************************************************/

  // f ∈ Θ(g) ⟹ Θ(f) ⊆ Θ(g)
  lemma lem_MonoIncr(f:nat->R0, g:nat->R0)  
    requires f in Th(g)
    ensures  Th(f) <= Th(g) 
  {
    forall h:nat->R0 | h in Th(f) 
      ensures h in Th(g) 
    {
      calc {
            h in Th(f);
        ==> { assert f in Th(g); 
              lem_Trans(h, f, g); }
            h in Th(g);
      }
    } 
  }

  // Reverse direction of lem_MonoIncr
  // f ∈ Θ(g) ⟹ Θ(g) ⊆ Θ(f)
  lemma lem_MonoIncrREV(f:nat->R0, g:nat->R0)  
    requires f in Th(g)
    ensures  Th(g) <= Th(f) 
  {
    lem_Sym(f, g);
    lem_MonoIncr(g, f);  
  }  

  // Join previous facts into an equivalence
  // f ∈ Θ(g) ⟹ Θ(f) = Θ(g)
  lemma lem_MonoIncrEQ(f:nat->R0, g:nat->R0)  
    requires f in Th(g)
    ensures  Th(g) == Th(f) 
  {
    lem_MonoIncr(f, g);  
    lem_MonoIncrREV(f, g);  
  }  

  /******************************************************************************
    Closure properties from the set-theoretic view
  ******************************************************************************/

  // lem_Scale lifted to sets
  // f ∈ Θ(g) ∧ a > 0 ⟹ Θ(a*f) = Θ(g)
  lemma lem_ScaleSet(f:nat->R0, g:nat->R0, a:R0)
    requires f in Th(g) 
    requires a > 0.0
    ensures  Th(n => a*f(n)) == Th(g) 
  {  
    assert (n => a*f(n)) in Th(g) 
      by { lem_Scale(f, g, a); }    
    lem_MonoIncrEQ(n => a*f(n), g);
  }

  // lem_Sum lifted to sets
  // f1 ∈ Θ(g1) ∧ f2 ∈ Θ(g2) ==> Θ(f1+f2) = Θ(g1+g2)
  lemma lem_SumSet(f1:nat->R0, g1:nat->R0, f2:nat->R0, g2:nat->R0) 
    requires f1 in Th(g1) 
    requires f2 in Th(g2) 
    ensures  Th(n => f1(n)+f2(n)) == Th(n => g1(n)+g2(n)) 
  {  
    assert (n => f1(n)+f2(n)) in Th(n => g1(n)+g2(n)) 
      by { lem_Sum(f1, g1, f2, g2); }    
    lem_MonoIncrEQ(n => f1(n)+f2(n), n => g1(n)+g2(n));
  }  
  
  /******************************************************************************
    Equivalence properties (on classes)
  ******************************************************************************/

  // Θ(f) = Θ(g) induces an equivalence relation on functions

  // Equivalence of representatives
  // Θ(f) = Θ(g) ⟹ f ∈ Θ(g) ∧ g ∈ Θ(f)
  lemma lem_EqRepr(f:nat->R0, g:nat->R0)  
    requires Th(f) == Th(g)
    ensures  f in Th(g) && g in Th(f)
  { 
    assert f in Th(f) by { lem_Refl(f); }
    assert g in Th(g) by { lem_Refl(g); }
  }

  /******************************************************************************
    Congruence properties
  ******************************************************************************/

  // These show that equivalence is preserved under operations or relations

  // Congruence of membership
  // Θ(f) = Θ(g) ∧ f ∈ Θ(h) ⟹ g ∈ Θ(h)
  lemma lem_CongEq(f:nat->R0, g:nat->R0, h:nat->R0)  
    requires Th(f) == Th(g)
    requires f in Th(h)
    ensures  g in Th(h) 
  {
    lem_EqRepr(f, g);
    assert g in Th(f);
    assert f in Th(h);
    lem_Trans(g, f, h);
  }

  // Congruence of order
  // Θ(f) = Θ(g) ∧ Θ(h) = Θ(k) ∧ f ∈ Θ(h) ⟹ g ∈ Θ(k)
  lemma lem_CongOrder(f:nat->R0, g:nat->R0, h:nat->R0, k:nat->R0)  
    requires Th(f) == Th(g)
    requires Th(h) == Th(k)
    requires f in Th(h)
    ensures  g in Th(k)  
    // TODO

  /******************************************************************************
    Zero functions and the class Θ(0)
  ******************************************************************************/

  // Any function eventually zero is Θ(0)
  lemma lem_EventuallyZeroGrowth(f:nat->R0, n0:nat)  
    requires EventuallyZero(f, n0)
    ensures  f in Th(zeroGrowth())
  {  
    LemOh.lem_EventuallyZeroGrowth(f, n0); 
    LemOm.lem_EventuallyZeroGrowth(f, n0); 
    lem_Def2ImpDef(f, zeroGrowth());
  }

  // Reverse direction of lem_EventuallyZeroGrowth
  // Any function in Θ(0) is eventually zero
  lemma lem_EventuallyZeroGrowthREV(f:nat->R0)  
    requires f in Th(zeroGrowth())  
    ensures  exists n0 :: EventuallyZero(f, n0)
  {  
    var c1:R0, c2:R0, n1:nat :| c1 > 0.0 && c2 > 0.0 && bigThFrom(c1, c2, n1, f, zeroGrowth());  
    assert H1: forall n:nat :: 0 <= n1 <= n ==> c1*zeroGrowth()(n) <= f(n) <= c2*zeroGrowth()(n);

    forall n:nat | n1 <= n
      ensures f(n) == 0.0
    { }
    assert EventuallyZero(f, n1);
    assert exists n0 :: EventuallyZero(f, n0);
  }  

  // Join previous facts into an equivalence
  // This serves as a characterization of the Θ(0) class
  // f in Θ(0) ⟺ f eventually zero
  lemma lem_EventuallyZeroGrowthIFF(f:nat->R0)  
    ensures f in Th(zeroGrowth()) <==> exists n0 :: EventuallyZero(f, n0)
  {  
    assert f in Th(zeroGrowth()) ==> exists n0 :: EventuallyZero(f, n0) by {
      if f in Th(zeroGrowth()) {
        lem_EventuallyZeroGrowthREV(f); 
      }
    }
    assert (exists n0 :: EventuallyZero(f, n0)) ==> f in Th(zeroGrowth()) by {
      if exists n0 :: EventuallyZero(f, n0) {
        var n0 :| EventuallyZero(f, n0);
        lem_EventuallyZeroGrowth(f, n0);
      }
    }    
  }  

  // Zero function is Θ(0)
  lemma lem_ZeroGrowth(f:nat->R0)  
    requires forall n:nat :: f(n) == 0.0
    ensures  f in Th(zeroGrowth())
  {  
    lem_EventuallyZeroGrowth(f, 0); 
  }

  /******************************************************************************
    Const functions and the class Θ(1)
  ******************************************************************************/

  // Any function eventually non-zero const is Θ(1)
  // Note: the reverse doesn't hold
  lemma lem_EventuallyConstGrowth(f:nat->R0, a:R0, n0:nat)  
    requires a > 0.0
    requires EventuallyConst(f, a, n0)
    ensures  f in Th(constGrowth())
  {  
    LemOh.lem_EventuallyConstGrowth(f, a, n0); 
    LemOm.lem_EventuallyConstGrowth(f, a, n0); 
    lem_Def2ImpDef(f, constGrowth());    
  }

  // Any non-zero const function is Θ(1)
  lemma lem_ConstGrowth(f:nat->R0, a:R0)  
    requires a > 0.0
    requires AlwaysConst(f, a)
    ensures  f in Th(constGrowth())
  {
     lem_EventuallyConstGrowth(f, a, 0);
  }  

  // Any function eventually bounded below by a non-zero const 
  // and eventually bounded above by a const is Θ(1)
  lemma lem_EventuallyBoundConstGrowth(f:nat->R0, a:R0, b:R0, n0:nat)  
    requires a > 0.0
    requires EventuallyConstBoundBelow(f, a, n0)
    requires EventuallyConstBoundAbove(f, b, n0)
    ensures  f in Th(constGrowth())
  {  
    LemOh.lem_EventuallyBoundConstGrowth(f, b, n0); 
    LemOm.lem_EventuallyBoundConstGrowth(f, a, n0); 
    lem_Def2ImpDef(f, constGrowth());    
  }

  // Reverse direction of lem_EventuallyBoundConstGrowth
  // Any function in Θ(1) is eventually bounded below by a non-zero const 
  // and eventually bounded above by a const
  lemma lem_EventuallyBoundConstGrowthREV(f:nat->R0)  
    requires f in Th(constGrowth())
    ensures exists a, n0 :: a > 0.0 && EventuallyConstBoundBelow(f, a, n0)
    ensures exists a, n0 :: EventuallyConstBoundAbove(f, a, n0)
  {  
    lem_DefImpDef2(f, constGrowth());  
    LemOh.lem_EventuallyBoundConstGrowthREV(f);
    LemOm.lem_EventuallyBoundConstGrowthREV(f); 
  }

  // Join previous facts into an equivalence
  // This serves as a characterization of the Θ(1) class
  // f in Θ(1) ⟺ f eventually bounded below by a non-zero const 
  //                and eventually bounded above by a const
  lemma lem_EventuallyBoundConstGrowthIFF(f:nat->R0)  
    ensures f in Th(constGrowth()) 
            <==> (   (exists a, n0 :: a > 0.0 && EventuallyConstBoundBelow(f, a, n0))
                  && (exists a, n0 :: EventuallyConstBoundAbove(f, a, n0)))
  {  
    var E1 := exists a, n0 :: a > 0.0 && EventuallyConstBoundBelow(f, a, n0);
    var E2 := exists a, n0 :: EventuallyConstBoundAbove(f, a, n0);

    assert f in Th(constGrowth()) ==> E1 && E2 by {
      if f in Th(constGrowth()) { 
        lem_EventuallyBoundConstGrowthREV(f); 
      }
    }
    assert E1 && E2 ==> f in Th(constGrowth()) by {
      if E1 && E2 {
        var a1, n10 :| a1 > 0.0 && EventuallyConstBoundBelow(f, a1, n10);
        var a2, n20 :| EventuallyConstBoundAbove(f, a2, n20);
        LemOm.lem_EventuallyBoundConstGrowth(f, a1, n10);
        LemOh.lem_EventuallyBoundConstGrowth(f, a2, n20);
        lem_Def2ImpDef(f, constGrowth()); 
      }
    }     
  }    

  /******************************************************************************
    Logarithms and the class Θ(log_b)
  ******************************************************************************/

  // The base of log doesn't change asymptotics
  // b1,b2 > 0 ⟹ (h ∈ Θ(log_b1) ⟺ h ∈ Θ(log_b2))
  lemma lem_LogBase(b1:real, b2:real, h:nat->R0)  
    requires b1 > 1.0 && b2 > 1.0
    requires h in Th(logGrowth(b1))
    ensures  h in Th(logGrowth(b2))
  {
    assert A: h in O(logGrowth(b1)) && h in Om(logGrowth(b1))
      by { lem_DefImpDef2(h, logGrowth(b1)); }

    assert B: h in O(logGrowth(b2)) 
      by { reveal A; LemOh.lem_LogBase(b1, b2, h); }

    assert C: h in Om(logGrowth(b2)) 
      by { reveal A; LemOm.lem_LogBase(b1, b2, h); }

    assert h in Th(logGrowth(b2)) 
      by { reveal B, C; lem_Def2ImpDef(h, logGrowth(b2)); }    
  } 

  // b1,b2 > 0 ⟹ Θ(log_b1) = Θ(log_b2)
  lemma lem_LogBaseSet(b1:real, b2:real)  
    requires b1 > 1.0 && b2 > 1.0
    ensures  Th(logGrowth(b1)) == Th(logGrowth(b2))
  {
    forall h:nat->R0
      ensures h in Th(logGrowth(b1)) <==> h in Th(logGrowth(b2))
    {
      assert h in Th(logGrowth(b1)) ==> h in Th(logGrowth(b2)) by { 
        if h in Th(logGrowth(b1)) {
          lem_LogBase(b1, b2, h); 
        }
      }
      assert h in Th(logGrowth(b2)) ==> h in Th(logGrowth(b1)) by { 
        if h in Th(logGrowth(b2)) {
          lem_LogBase(b2, b1, h); 
        }
      }      
    }
  }

  /******************************************************************************
    For different growth rates the classes are disjoint (denoted here by ⊥).

      Θ(0) ⊥ Θ(1) ⊥ Θ(log_b)
                  ⊥ Θ(n^2) ⊥ Θ(n^3) ⊥ ... ⊥ Θ(n^k) 
                  ⊥ Θ(2^n) ⊥ Θ(3^n) ⊥ ... ⊥ Θ(b^n) 

    Proving Θ(f) ⊥ Θ(g) amounts to proving Θ(f) ∩ Θ(g) = ∅.               
  ******************************************************************************/

  // Θ(0) ⊥ Θ(1) 
  lemma lem_ZeroDisjConst()
    ensures Th(zeroGrowth()) * Th(constGrowth()) == emptyInfSet<nat->R0>()
  {
    forall f:nat->R0 | f in Th(zeroGrowth())
      ensures f !in Th(constGrowth())
    { 
      // By RAA, suppose f in Θ(1)
      if f in Th(constGrowth()) {
        lem_EventuallyZeroGrowthREV(f);
        var n0:nat :| EventuallyZero(f, n0);
        assert A: forall n:nat :: n >= n0 ==> f(n) == 0.0;

        lem_EventuallyBoundConstGrowthREV(f);
        var a, n1:nat :| a > 0.0 && EventuallyConstBoundBelow(f, a, n1);
        assert B: forall n:nat :: n >= n1 ==> f(n) >= a;
        
        var n:nat := max(n0, n1);
        assert f(n) == 0.0 by { reveal A; }
        assert f(n) >= a by { reveal B; }

        assert false;
      }
    }
  }

}