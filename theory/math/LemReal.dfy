/******************************************************************************
  Facts about real numbers
******************************************************************************/

module LemReal {

  // x < y ⟹ ∃ d > 0 : y = x + d
  lemma lem_PositiveDifference(x:real, y:real)
    requires x < y
    ensures  exists d:real {:trigger posPred(x,y,d)} :: d > 0.0 && y == x + d
  {
    var d := y - x;
    assert d > 0.0;
    assert y == x + d;
    assert posPred(x,y,d);
  } 

  ghost predicate posPred(x:real, y:real, d:real) {
    y == x + d
  }

}