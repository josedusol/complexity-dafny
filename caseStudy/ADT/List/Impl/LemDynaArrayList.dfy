include "../../../../theory/math/ExpReal.dfy"
include "../../../../theory/math/TypeR0.dfy"
include "../../../../theory/ComplexityR0.dfy"
include "../../../../theory/LemComplexityR0.dfy"

/******************************************************************************
  Auxiliary module for DynaArrayList verification
******************************************************************************/

module LemDynaArrayList {

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
    (4*N - k + 1) as R0
  }

  ghost function TinsertUp(N:nat) : R0
  {
    (4*N + 1) as R0
  }  

  ghost function Tinsert2(N:nat, k:nat) : R0
    requires N >= k
  {
    (N - k + 1) as R0
  }    

  ghost function Tinsert2Up(N:nat) : R0
  {
    (N + 1) as R0
  }    

  lemma lem_Insert_TinsertBigOlin() returns (c:R0, n0:nat) 
    ensures bigOfrom(c, n0, TinsertUp, linGrowth())
  {
    c, n0 := 2.0*4.0, 1;
    forall n:nat | 0 <= n0 <= n
      ensures TinsertUp(n) <= c*linGrowth()(n)
    {
      calc {
           TinsertUp(n);
        == (4*n + 1) as R0;
        <= c*n as R0;
        == { lem_expOne(n as R0); }
           c*exp(n as R0, 1.0);
        == c*linGrowth()(n);   
      }
    }
    assert bigOfrom(c, n0, TinsertUp, linGrowth());
  }

  lemma lem_Insert_Tinsert2BigOlin() returns (c:R0, n0:nat) 
    ensures bigOfrom(c, n0, Tinsert2Up, linGrowth())
  {
    c, n0 := 2.0, 1;
    forall n:nat | 0 <= n0 <= n
      ensures Tinsert2Up(n) <= c*linGrowth()(n)
    {
      calc {
           Tinsert2Up(n);
        == (n + 1) as R0;
        <= c*n as R0;
        == { lem_expOne(n as R0); }
           c*exp(n as R0, 1.0);
        == c*linGrowth()(n);   
      }
    }
    assert bigOfrom(c, n0, Tinsert2Up, linGrowth());
  }

  // Complexity analysis for Append operation 

  ghost function Tappend(N:nat) : R0
  {
    (3*N + 1) as R0
  }

  ghost function Tappend2(N:nat) : R0
  {
    1.0
  }  

  lemma lem_Append_TappendBigOlin() returns (c:R0, n0:nat) 
    ensures bigOfrom(c, n0, Tappend, linGrowth())
  {
    c, n0 := 2.0*3.0, 1;
    forall n:nat | 0 <= n0 <= n
      ensures Tappend(n) <= c*linGrowth()(n)
    {
      calc {
           Tappend(n);
        == (3*n + 1) as R0;
        <= c*n as R0;
        == { lem_expOne(n as R0); }
           c*exp(n as R0, 1.0);
        == c*linGrowth()(n);   
      }
    }
    assert bigOfrom(c, n0, Tappend, linGrowth());
  }

  lemma lem_Append_Tappend2BigOconst() returns (c:R0, n0:nat) 
    ensures bigOfrom(c, n0, Tappend2, constGrowth())
  {
    lem_bigO_constGrowth(Tappend2, 1.0);
    var c':R0, n0':nat :| bigOfrom(c', n0', Tappend2, constGrowth());
    c, n0 := c', n0';
  }  

  // Complexity analysis for Delete operation  

  ghost function Tdelete(N:nat) : R0 
  // TODO

}