include "../math/Function.dfy"
include "../math/LemFunction.dfy"
include "../math/TypeR0.dfy"
include "./Asymptotics.dfy"
include "./LemBigOh.dfy"

/******************************************************************************
  Algebra of Big Oh
******************************************************************************/

module LemBigOhAlgebra {

  import opened Function 
  import opened LemFunction
  import opened TypeR0 
  import opened Asymptotics
  import LemOh = LemBigOh

  // Closure under scaling
  // a*O(f) ⊆ O(f)
  lemma lem_Scale(f:nat->R0, a:R0) 
    requires a > 0.0
    ensures scaleSet(a, O(f)) <= O(f) 
  { 
    forall h:nat->R0 | h in scaleSet(a, O(f))
      ensures h in O(f)
    {
      var f1 :| f1 in O(f) && h == (n => a * f1(n));  // h = a*f1
      LemOh.lem_Scale(f1, f, a);  // f1 ∈ O(f) ∧ a > 0 ⟹ a*f1 ∈ O(f) 
    } 
  }   

  // Reverse direction of lem_Scale
  // O(f) ⊆ a*O(f)
  lemma lem_ScaleREV(f:nat->R0, a:R0) 
    requires a > 0.0
    ensures O(f) <= scaleSet(a, O(f))
  { 
    forall h:nat->R0 | h in O(f)
      ensures h in scaleSet(a, O(f)) 
    {
      var f1:nat->R0 := n => 1.0/a * h(n);
      assert A: f1 in O(f) by {
        assert h in O(f) && 1.0/a > 0.0;
        LemOh.lem_Scale(h, f, 1.0/a);
      }
      assert B: h == n => a * f1(n) by {
        lem_Exten(h, n => a * f1(n)) by {
          lem_EtaApp(h); 
          forall n ensures h(n) == (n => a * f1(n))(n) { }    
        }
      }
      assert exists f1 :: f1 in O(f) && h == (n => a * f1(n)) 
        by { reveal A, B; }
    } 
  }    

  // Join previous facts into an equivalence
  // a*O(f) = O(f)
  lemma lem_ScaleEQ(f:nat->R0, a:R0) 
    requires a > 0.0
    ensures scaleSet(a, O(f)) == O(f) 
  {
    lem_Scale(f, a);
    lem_ScaleREV(f, a);
  } 

  // Closure under addition
  // O(f) + O(g) ⊆ O(f + g)
  lemma lem_Sum(f:nat->R0, g:nat->R0) 
    ensures sumSet(O(f), O(g)) <= O(n => f(n) + g(n)) 
  { 
    forall h:nat->R0 | h in sumSet(O(f), O(g))
      ensures h in O(n => f(n) + g(n))
    {
      var f1, f2 :| f1 in O(f) && f2 in O(g) && h == (n => f1(n) + f2(n));  // h = f1+f2
      LemOh.lem_Sum(f1, f, f2, g);  // f1 ∈ O(f) ∧ f2 ∈ O(g) ⟹ f1+f2 ∈ O(f+g)  
    } 
  } 

  // Closure under multiplication
  // O(f) * O(g) ⊆ O(f * g)
  lemma lem_Mul(f:nat->R0, g:nat->R0) 
    ensures mulSet(O(f), O(g)) <= O(n => f(n) * g(n)) 
  { 
    forall h:nat->R0 | h in mulSet(O(f), O(g))
      ensures h in O(n => f(n) * g(n))
    {
      var f1, f2 :| f1 in O(f) && f2 in O(g) && h == (n => f1(n) * f2(n));  // h = f1*f2
      LemOh.lem_Mul(f1, f, f2, g);  // f1 ∈ O(f) ∧ f2 ∈ O(g) ⟹ f1*f2 ∈ O(f*g)  
    }
  }   

}