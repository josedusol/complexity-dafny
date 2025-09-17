include "../math/Function.dfy"
include "../math/LemFunction.dfy"
include "../math/TypeR0.dfy"
include "./Asymptotics.dfy"
include "./LemBigOh.dfy"
include "./LemBigOm.dfy"
include "./LemBigTh.dfy"

/******************************************************************************
  Algebra of Big Theta
******************************************************************************/

module LemBigThAlgebra {

  import opened Function 
  import opened LemFunction 
  import opened TypeR0 
  import opened Asymptotics
  import LemOh = LemBigOh
  import LemOm = LemBigOm
  import LemTh = LemBigTh

  // Closure under scaling
  // a*Θ(f) ⊆ Θ(f)
  lemma lem_Scale(f:nat->R0, a:R0) 
    requires a > 0.0
    ensures scaleSet(a, Th(f)) <= Th(f) 
  { 
    forall h:nat->R0 | h in scaleSet(a, Th(f))
      ensures h in Th(f)
    {
      var f1 :| f1 in Th(f) && h == (n => a * f1(n));  // h = a*f1
      LemTh.lem_Scale(f1, f, a);  // f1 ∈ Θ(f) ∧ a > 0 ⟹ a*f1 ∈ Θ(f) 
    }  
  }   

  // Reverse direction of lem_Scale
  // Θ(f) ⊆ a*Θ(f)
  lemma lem_ScaleREV(f:nat->R0, a:R0) 
    requires a > 0.0
    ensures Th(f) <= scaleSet(a, Th(f))
  { 
    forall h:nat->R0 | h in Th(f)
      ensures h in scaleSet(a, Th(f)) 
    {
      var f1:nat->R0 := n => 1.0/a * h(n);
      assert A: f1 in Th(f) by {
        assert h in Th(f) && 1.0/a > 0.0;
        LemTh.lem_Scale(h, f, 1.0/a);
      }
      assert B: h == n => a * f1(n) by {
        lem_Exten(h, n => a * f1(n)) by {
          lem_EtaApp(h); 
          forall n ensures h(n) == (n => a * f1(n))(n) { }    
        }
      }
      assert exists f1 :: f1 in Th(f) && h == (n => a * f1(n)) 
        by { reveal A, B; }
    } 
  }

  // Join previous facts into an equivalence
  // a*Θ(f) = Θ(f)
  lemma lem_ScaleEQ(f:nat->R0, a:R0) 
    requires a > 0.0
    ensures scaleSet(a, Th(f)) == Th(f) 
  {
    lem_Scale(f, a);
    lem_ScaleREV(f, a);
  } 
 
  // Closure under addition
  // Θ(f) + Θ(g) ⊆ Θ(f + g)
  lemma lem_Sum(f:nat->R0, g:nat->R0) 
    ensures sumSet(Om(f), Om(g)) <= Om(n => f(n) + g(n)) 
  // TODO
    
  // Closure under multiplication    
  // Θ(f) * Θ(g) ⊆ Θ(f * g)
  lemma lem_Mul(f:nat->R0, g:nat->R0) 
    ensures mulSet(Om(f), Om(g)) <= Om(n => f(n) * g(n)) 
  // TODO
}