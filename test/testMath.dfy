
include "../theory/math.dfy"
include "../theory/mathSum.dfy"

ghost method test_sumrInterval() {
  reveal sumr();
  var s := sumr(0, 2, x => 1.0);
  assert s == 3.0; 
}

ghost method test_sumInterval() {
  reveal sum();
  var s := sum(0, 2, x => 1);
  assert s == 3; 
}

ghost method test_sumSeq() {
  reveal sumSeq();
  var s := sumSeq([0,1,2], x => 1.0);
  assert s == 3.0; 
}
 
ghost method test_sumSet() {
  reveal sumSet();
  var s2 := sumSet({0,1,2}, x => 1.0);
  // assert s2 == 3.0;  // not working
}
