include "../../../../theory/math/ExpReal.dfy"
include "../../../../theory/math/TypeR0.dfy"
include "../../../../theory/Complexity/Asymptotics.dfy"
include "../../../../theory/Complexity/LemBigOh.dfy"

/******************************************************************************
  Auxiliary module for DynaArrayList verification
******************************************************************************/

module LemDynaArrayList {

  import opened ExpReal
  import opened TypeR0
  import opened Asymptotics
  import opened LemBigOh

  /******************************************************************************
    Complexity analysis for Get operation  
  ******************************************************************************/

  ghost function Tget(N:nat) : R0
  {
    1.0
  }

  lemma lem_Get_TgetBigOconst()
    ensures exists c:R0, n0:nat :: c > 0.0 && bigOhFrom(c, n0, Tget, constGrowth())
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
    assert bigOhFrom(c, n0, Tget, constGrowth());
  }

  /******************************************************************************
    Complexity analysis for Grow operation 
  ******************************************************************************/

  ghost function Tgrow(m:nat, C:nat, N:nat) : R0
  {
    (m*C + N) as R0
  }

  lemma lem_Grow_TgrowBigOlin(m:nat) returns (c:R0, n0:nat) 
    ensures c > 0.0 && bigOhFrom(c, n0, (C => Tgrow(m,C,C)), linGrowth())
  {
      c, n0 := (m+1) as R0, 1;
      forall n:nat | 0 <= n0 <= n
        ensures (C => Tgrow(m,C,C))(n) <= c*linGrowth()(n)
      {
        calc {
             (C => Tgrow(m,C,C))(n);
          == (m*n + n) as R0;
          == ((m+1)*n) as R0;
          == c*linGrowth()(n);   
        }
      }
      assert bigOhFrom(c, n0, (C => Tgrow(m,C,C)), linGrowth());
  }

  /******************************************************************************
    Complexity analysis for Insert operation 
  ******************************************************************************/

  ghost function Tinsert(m:nat, N:nat, k:nat) : R0
    requires N >= k
  {
    ((m+2)*N - k + 1) as R0
  }

  ghost function TinsertUp(m:nat, N:nat) : R0
  {
    ((m+2)*N + 1) as R0
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

  lemma lem_Insert_TinsertBigOlin(m:nat) returns (c:R0, n0:nat) 
    ensures c > 0.0 && bigOhFrom(c, n0, (N => TinsertUp(m,N)), linGrowth())
  {
    c, n0 := 2.0 * (m+2) as R0, 1;
    forall n:nat | 0 <= n0 <= n
      ensures (N => TinsertUp(m,N))(n) <= c*linGrowth()(n)
    {
      calc {
           (N => TinsertUp(m,N))(n);
        == ((m+2)*n + 1) as R0;
        <= c*n as R0;
        == c*linGrowth()(n);   
      }
    }
    assert bigOhFrom(c, n0, (N => TinsertUp(m,N)), linGrowth());
  }

  lemma lem_Insert_Tinsert2BigOlin() returns (c:R0, n0:nat) 
    ensures c > 0.0 && bigOhFrom(c, n0, Tinsert2Up, linGrowth())
  {
    c, n0 := 2.0, 1;
    forall n:nat | 0 <= n0 <= n
      ensures Tinsert2Up(n) <= c*linGrowth()(n)
    {
      calc {
           Tinsert2Up(n);
        == (n + 1) as R0;
        <= c*n as R0;
        == c*linGrowth()(n);   
      }
    }
    assert bigOhFrom(c, n0, Tinsert2Up, linGrowth());
  }

  /******************************************************************************
    Complexity analysis for Append operation 
  ******************************************************************************/

  ghost function Tappend(m:nat, N:nat) : R0
  {
    ((m+1)*N + 1) as R0
  }

  ghost function Tappend2(N:nat) : R0
  {
    1.0
  }  

  lemma lem_Append_TappendBigOlin(m:nat) returns (c:R0, n0:nat) 
    ensures c > 0.0 && bigOhFrom(c, n0, (N => Tappend(m,N)), linGrowth())
  {
    c, n0 := 2.0 * (m+1) as R0, 1;
    forall n:nat | 0 <= n0 <= n
      ensures (N => Tappend(m,N))(n) <= c*linGrowth()(n)
    {
      calc {
           (N => Tappend(m,N))(n);
        == ((m+1)*n + 1) as R0;
        <= c*n as R0;
        == c*linGrowth()(n);   
      }
    }
    assert bigOhFrom(c, n0, (N => Tappend(m,N)), linGrowth());
  }

  lemma lem_Append_Tappend2BigOconst() returns (c:R0, n0:nat) 
    ensures c > 0.0 && bigOhFrom(c, n0, Tappend2, constGrowth())
  {
    lem_ConstGrowth(Tappend2, 1.0);
    var c':R0, n0':nat :| c' > 0.0 && bigOhFrom(c', n0', Tappend2, constGrowth());
    c, n0 := c', n0';
  }  

  /******************************************************************************
    Complexity analysis for Delete operation 
  ******************************************************************************/

  ghost function Tdelete(N:nat, k:nat) : R0 
    requires N >= k+1
  {
    (N - k - 1) as R0
  }

  ghost function Tdelete2(N:nat) : R0 
  {
    N as R0
  }

  lemma lem_Delete_Tdelete2BigOlin() returns (c:R0, n0:nat) 
    ensures c > 0.0 && bigOhFrom(c, n0, Tdelete2, linGrowth())
  {
    c, n0 := 1.0, 1;
    forall n:nat | 0 <= n0 <= n
      ensures Tdelete2(n) <= c*linGrowth()(n)
    {
      calc {
           Tdelete2(n);
        == n as R0;
        <= c*n as R0;
        == c*linGrowth()(n);
      }
    }
    assert bigOhFrom(c, n0, Tdelete2, linGrowth());
  }

}