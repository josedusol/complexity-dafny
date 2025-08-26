include "../../../../theory/math/ExpReal.dfy"
include "../../../../theory/math/TypeR0.dfy"
include "../../../../theory/ComplexityR0.dfy"

/******************************************************************************
  Auxiliary module for ArrayList verification
******************************************************************************/

module LemArrayList {

  import opened ExpReal
  import opened TypeR0
  import opened ComplexityR0

  // Complexity analysis for Get operation  

  ghost function costGet(N:nat) : R0
  {
    1.0
  }

  lemma lem_costGetBigOconst()
    ensures exists c:R0, n0:nat :: bigOfrom(c, n0, costGet, constGrowth())
  {
    var c, n0 := 1.0, 0;
    forall n:nat | 0 <= n0 <= n
      ensures costGet(n) <= c*constGrowth()(n)
    {
      calc {
           costGet(n);
        == 1.0;
        <= c*1.0;
        == c*constGrowth()(n);   
      }
    }
    assert bigOfrom(c, n0, costGet, constGrowth());
  }

  // Complexity analysis for Insert operation 

  ghost function costInsert(N:nat) : R0
  {
    N as R0
  }

  lemma lem_costInsertBigOlin() returns (c:R0, n0:nat) 
    ensures bigOfrom(c, n0, costInsert, linGrowth())
  {
    c, n0 := 1.0, 1;
    forall n:nat | 0 <= n0 <= n
      ensures costInsert(n) <= c*linGrowth()(n)
    {
      calc {
           costInsert(n);
        == n as R0;
        <= c*n as R0;
        == { lem_expOne(n as R0); }
           c*exp(n as R0, 1.0);
        == c*linGrowth()(n);   
      }
    }
    assert bigOfrom(c, n0, costGet, linGrowth());
  }

  // Complexity analysis for Delete operation  

  ghost function costDelete(N:nat) : R0 
  // TODO

}