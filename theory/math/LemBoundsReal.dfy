include "./ExpReal.dfy"
include "./LogReal.dfy"
include "./Root2Real.dfy"

/******************************************************************************
  Bounds of mathematical functions over reals
******************************************************************************/

module LemBoundsReal {
  
  import Exp = ExpReal
  import R2R = Root2Real
  import RR  = RootReal

  // 1 < sqrt(2) < 2
  lemma lem_1LqSqrt2Lq2()
    ensures 1.0 < R2R.sqrt(2.0) < 2.0
  { 
    assert R2R.sqrt(2.0) < 2.0 by {
      calc { 
             R2R.sqrt(2.0) < 2.0;
        <==> { Exp.lem_BaseStrictIncrIFF(2.0, R2R.sqrt(2.0), 2.0); } 
             Exp.exp(R2R.sqrt(2.0), 2.0) < Exp.exp(2.0, 2.0);
        <==> { reveal Exp.exp2(); Exp.lem_Exp2FirstValues(); }
             Exp.exp(R2R.sqrt(2.0), 2.0) < 4.0;
        <==> { reveal R2R.sqrt(); RR.lem_PowRootInverse(2.0, 2.0); }
             2.0 < 4.0;
      }
    }
    assert 1.0 < R2R.sqrt(2.0) by {
      calc { 
             1.0 < R2R.sqrt(2.0);
        <==> { Exp.lem_BaseStrictIncrIFF(2.0, 1.0, R2R.sqrt(2.0)); } 
             Exp.exp(1.0, 2.0) < Exp.exp(R2R.sqrt(2.0), 2.0); 
        <==> { Exp.lem_BaseOne(2.0); }
             1.0 < Exp.exp(R2R.sqrt(2.0), 2.0);
        <==> { reveal R2R.sqrt(); RR.lem_PowRootInverse(2.0, 2.0); }
             1.0 < 2.0;
      }
    }
  } 

}
