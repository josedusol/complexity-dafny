include "../math/Function.dfy"
include "../math/LemFunction.dfy"
include "../math/TypeR0.dfy"
include "./Asymptotics.dfy"
include "./LemBigOm.dfy"

/******************************************************************************
  Algebra of Big Omega
******************************************************************************/

module LemBigOhAlgebra {

  import opened Function 
  import opened LemFunction
  import opened TypeR0
  import opened Asymptotics
  import LemOm = LemBigOm

  // Closure under scaling
  // a*Ω(f) ⊆ Ω(f)
  lemma lem_Scale(f:nat->R0, a:R0) 
    requires a > 0.0
    ensures scaleSet(a, Om(f)) <= Om(f) 
  { 
    forall h:nat->R0 | h in scaleSet(a, Om(f))
      ensures h in Om(f)
    {
      var f1 :| f1 in Om(f) && h == (n => a * f1(n));  // h = a*f1
      LemOm.lem_Scale(f1, f, a);  // f1 ∈ Ω(f) ∧ a > 0 ⟹ a*f1 ∈ Ω(f) 
    } 
  }  

  // Reverse direction of lem_Scale
  // Ω(f) ⊆ a*Ω(f)
  lemma lem_ScaleREV(f:nat->R0, a:R0) 
    requires a > 0.0
    ensures Om(f) <= scaleSet(a, Om(f))
  { 
    forall h:nat->R0 | h in Om(f)
      ensures h in scaleSet(a, Om(f)) 
    {
      var f1:nat->R0 := n => 1.0/a * h(n);
      assert A: f1 in Om(f) by {
        assert h in Om(f) && 1.0/a > 0.0;
        LemOm.lem_Scale(h, f, 1.0/a);
      }
      assert B: h == n => a * f1(n) by {
        lem_Exten(h, n => a * f1(n)) by {
          lem_EtaApp(h); 
          forall n ensures h(n) == (n => a * f1(n))(n) { }    
        }
      }
      assert exists f1 :: f1 in Om(f) && h == (n => a * f1(n)) 
        by { reveal A, B; }
    } 
  }

  // Join previous facts into an equivalence
  // a*Ω(f) = Ω(f)
  lemma lem_ScaleEQ(f:nat->R0, a:R0) 
    requires a > 0.0
    ensures scaleSet(a, Om(f)) == Om(f) 
  {
    lem_Scale(f, a);
    lem_ScaleREV(f, a);
  } 

  // Closure under addition
  // Ω(f) + Ω(g) ⊆ Ω(f + g)
  lemma lem_Sum(f:nat->R0, g:nat->R0) 
    ensures sumSet(Om(f), Om(g)) <= Om(n => f(n) + g(n)) 
  // TODO  

  // Closure under multiplication  
  // Ω(f) * Ω(g) ⊆ Ω(f * g)
  lemma lem_Mul(f:nat->R0, g:nat->R0) 
    ensures mulSet(Om(f), Om(g)) <= Om(n => f(n) * g(n)) 
  // TODO

}