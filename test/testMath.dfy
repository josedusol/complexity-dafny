
include "../theory/math.dfy"

ghost method test_sumInterval() {
  reveal sum();
  var s := sum(0, 2, x => 1);
  assert s == 3; 
}

ghost method test_sumSeq() {
  var s := sumSeq([0,1,2], x => 1);
  assert s == 3; 
}

ghost method test_sumSet() {
  var s2 := sumSet({0,1,2}, x => 1);
  // assert s2 == 3; // no funciona
} 
