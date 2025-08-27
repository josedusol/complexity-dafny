include "../../../../theory/math/ExpReal.dfy"
include "../../../../theory/math/TypeR0.dfy"
include "../../../../theory/ComplexityR0.dfy"

/******************************************************************************
  Auxiliary module for DynaArrayList verification
******************************************************************************/

module LemDynaArrayList {

  import opened ExpReal
  import opened TypeR0
  import opened ComplexityR0

  // Complexity analysis for Get operation  

  ghost function Tget(N:nat) : R0
  {
    1.0
  }

  lemma lem_Get_TgetBigOconst()
    ensures exists c:R0, n0:nat :: bigOfrom(c, n0, Tget, constGrowth())
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

  // Complexity analysis for Grow operation 


  ghost function Tgrow(m:nat, N:nat, n:nat) : R0
  {
    (m*N + n) as R0
  }

  lemma lem_Grow_TgrowBigOlin(m:nat) returns (c:R0, n0:nat) 
    ensures bigOfrom(c, n0, (N => Tgrow(m,N,N)), linGrowth())
  {
      c, n0 := (m+1) as R0, 1;
      forall n:nat | 0 <= n0 <= n
        ensures (N => Tgrow(m,N,N))(n) <= c*linGrowth()(n)
      {
        calc {
             (N => Tgrow(m,N,N))(n);
          == (m*n + n) as R0;
          == ((m+1)*n) as R0;
          == { lem_expOne(n as R0); }
            c*exp(n as R0, 1.0);
          == c*linGrowth()(n);   
        }
      }
      assert bigOfrom(c, n0, (N => Tgrow(m,N,N)), linGrowth());
  }

  // Complexity analysis for Insert operation 

  ghost function Tinsert(N:nat, k:nat) : R0
    requires N >= k
  {
    (4*N - k) as R0
  }

  ghost function Tinsert2(N:nat) : R0
  {
    (4*N) as R0
  }  

  lemma lem_Insert_Tinsert2BigOlin(k:nat) returns (c:R0, n0:nat) 
    ensures bigOfrom(c, n0, Tinsert2, linGrowth())
  {
    c, n0 := 4.0, 1;
    forall n:nat | 0 <= n0 <= n
      ensures Tinsert2(n) <= c*linGrowth()(n)
    {
      calc {
           Tinsert2(n);
        == (4*n) as R0;
        <= c*n as R0;
        == { lem_expOne(n as R0); }
           c*exp(n as R0, 1.0);
        == c*linGrowth()(n);   
      }
    }
    assert bigOfrom(c, n0, Tinsert2, linGrowth());
  }

  // Complexity analysis for Delete operation  

  ghost function Tdelete(N:nat) : R0 
  // TODO

}