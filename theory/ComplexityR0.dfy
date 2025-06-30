include "./math/ExpReal.dfy"
include "./math/LemFunction.dfy"
include "./math/TypeR0.dfy"

/**************************************************************************
  Complexity definitions lifted for non-negative real codomain
**************************************************************************/

module ComplexityR0 { 
  import opened ExpReal
  import opened LemFunction 
  import opened TypeR0 

  ghost predicate bigO(f:nat->R0, g:nat->R0)
  { 
    exists c:R0, n0:nat :: bigOfrom(c, n0, f, g) 
  }

  ghost predicate bigOfrom(c:R0, n0:nat, f:nat->R0, g:nat->R0)
  {
    forall n:nat :: 0 <= n0 <= n ==> f(n) <= c*g(n)
  }

  ghost predicate tIsBigO(n:nat, t:R0, g:nat->R0)
  { 
    exists f:nat->R0 :: t <= f(n) && bigO(f,g)
  }

  ghost predicate isBigOPoly(f:nat->R0)
  { 
    exists k:R0 :: bigO(f, n => pow(n as R0, k))
  }

  /**************************************************************************
    Basic O properties
  **************************************************************************/

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

}