include "../theory/math/SumInt.dfy"
include "../theory/math/SumReal.dfy"
include "../theory/math/SumSeqReal.dfy"
include "../theory/math/SumSetReal.dfy"

import Int  = SumInt
import Real = SumReal
import SeqR = SumSeqReal 
import SetR = SumSetReal

ghost method test_sumrInterval() {
  reveal Real.sum();
  var s := Real.sum(0, 2, x => 1.0);
  assert s == 3.0; 
}

ghost method test_sumInterval() {
  reveal Int.sum();
  var s := Int.sum(0, 2, x => 1);
  assert s == 3; 
}

ghost method test_sumSeq() {
  reveal SeqR.sum();
  var s := SeqR.sum([0,1,2], x => 1.0);
  assert s == 3.0; 
}
 
ghost method test_sumSet() {
  reveal SetR.sum();
  var s2 := SetR.sum({0,1,2}, x => 1.0);
  // assert s2 == 3.0;  // not working
}

lemma test_sumProperty(){
  var s := Real.sum(0, 3, x => 1.0);
  
  assert Real.sum(0, 3, x => 1.0) == 1.0 + Real.sum(1, 3, x => 1.0)
    by { reveal Real.sum(); }

  assert Real.sum(0, 3, x => x as real) == Real.sum(0, 2, x => x as real) + 3.0
    by { Real.lem_DropLast(0, 2, x => x as real); } 

}