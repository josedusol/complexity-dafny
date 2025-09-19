/******************************************************************************
  Sum over integer sets and real codomain
******************************************************************************/

module SumSetReal {

  // Σ_{s}f
  opaque ghost function sum(s:set<int>, f:int->real): real
    decreases s
  {
    if |s| == 0 
    then 0.0
    else var x :| x in s;
         f(x) + sum(s - {x}, f)
  }

}