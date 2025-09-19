include "../theory/math/intervalOp/SumReal.dfy"

import opened SumReal

lemma test_sumInterval() {
  var s := sum(0, 2, x => 1.0);
  reveal ISR.bigOp();
  assert s == 3.0;
}    

lemma test_sumProperty() {
  var s := sum(0, 3, x => 1.0);
  
  assert sum(0, 3, x => 1.0) == 1.0 + sum(1, 3, x => 1.0)
    by { ISR.lem_SplitFirst(0, 3, x => 1.0); }

  //assert op(1.0,2.0) == 3.0;

  assert sum(0, 3, x => 1.0) == sum(0, 2, x => 1.0) + 1.0
    by { ISR.lem_SplitLast(0, 3, x => 1.0); }     
  
}
