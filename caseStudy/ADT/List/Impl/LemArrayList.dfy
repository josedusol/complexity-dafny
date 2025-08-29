include "../../../../theory/math/ExpReal.dfy"
include "../../../../theory/math/TypeR0.dfy"
include "../../../../theory/ComplexityR0.dfy"
include "../../../../theory/LemComplexityR0.dfy"

/******************************************************************************
  Auxiliary module for ArrayList verification
******************************************************************************/

module LemArrayList {

  import opened ExpReal
  import opened TypeR0
  import opened ComplexityR0
  import opened LemComplexityR0

  // Complexity analysis for Get operation  

  ghost function Tget(N:nat) : R0
  {
    1.0
  }

  lemma lem_Get_TgetBigOconst()
    ensures exists c:R0, n0:nat :: c > 0.0 && bigOfrom(c, n0, Tget, constGrowth())
  {
    var c, n0 := 1.0, 0;
    forall n:nat | 0 <= n0 <= n
      ensures Tget(n) <= c*constGrowth()(n)
    {
      calc {
           Tget(n);
        == 1.0;
        <= c*1.0;
        == c*constGrowth()(n);   
      }
    }
    assert bigOfrom(c, n0, Tget, constGrowth());
  }

  // Complexity analysis for Insert operation 

  ghost function Tinsert(N:nat, k:nat) : R0
    requires N >= k
  {
    (N - k + 1) as R0
  }

  ghost function Tinsert2(N:nat) : R0
  {
    (N + 1) as R0
  }  

  lemma lem_Insert_Tinsert2BigOlin() returns (c:R0, n0:nat) 
    ensures c > 0.0 && bigOfrom(c, n0, Tinsert2, linGrowth())
  {
    c, n0 := 2.0, 1;
    forall n:nat | 0 <= n0 <= n
      ensures Tinsert2(n) <= c*linGrowth()(n)
    {
      calc {
           Tinsert2(n);
        == (n + 1) as R0;
        <= c*n as R0;
        == { lem_expOne(n as R0); }
           c*exp(n as R0, 1.0);
        == c*linGrowth()(n);   
      }
    }
    assert bigOfrom(c, n0, Tinsert2, linGrowth());
  }

  // Complexity analysis for Append operation 

  ghost function Tappend(N:nat) : R0
  {
    1.0
  }

  lemma lem_Append_TappendBigOconst() returns (c:R0, n0:nat) 
    ensures c > 0.0 &&bigOfrom(c, n0, Tappend, constGrowth())
  {
    lem_bigO_constGrowth(Tappend, 1.0);
    var c':R0, n0':nat :| c' > 0.0 && bigOfrom(c', n0', Tappend, constGrowth());
    c, n0 := c', n0';
  }

  // Complexity analysis for Delete operation  

  ghost function Tdelete(N:nat) : R0 
  // TODO

}