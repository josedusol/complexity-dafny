include "./ExpReal.dfy"
include "./LogReal.dfy"
include "./Root2Real.dfy"

/******************************************************************************
  Bounds of mathematical functions over reals
******************************************************************************/

module LemBoundsReal {
  
  import opened ExpReal
  import opened Root2Real
  import opened RootReal

  // 1 < sqrt(2) < 2
  lemma lem_root_1LQsqrt2LQ2()
    ensures 1.0 < sqrt(2.0) < 2.0
  { 
    assert sqrt(2.0) < 2.0 by {
      calc { 
             sqrt(2.0) < 2.0;
        <==> { lem_exp_BaseStrictIncrIFF(2.0, sqrt(2.0), 2.0); } 
             exp(sqrt(2.0), 2.0) < exp(2.0, 2.0);
        <==> { reveal exp2(); lem_exp2_FirstValues(); }
             exp(sqrt(2.0), 2.0) < 4.0;
        <==> { reveal sqrt(); lem_PowRoot_Inverse(2.0, 2.0); }
             2.0 < 4.0;
      }
    }
    assert 1.0 < sqrt(2.0) by {
      calc { 
             1.0 < sqrt(2.0);
        <==> { lem_exp_BaseStrictIncrIFF(2.0, 1.0, sqrt(2.0)); } 
             exp(1.0, 2.0) < exp(sqrt(2.0), 2.0); 
        <==> { lem_exp_BaseOne(2.0); }
             1.0 < exp(sqrt(2.0), 2.0);
        <==> { reveal sqrt(); lem_PowRoot_Inverse(2.0, 2.0); }
             1.0 < 2.0;
      }
    }
  } 

}
