/******************************************************************************
  Sum over integer sequences and real codomain
******************************************************************************/

module SumSeqReal {

  // Σ_{s}f
  opaque ghost function sum(s:seq<int>, f:int->real): real
    decreases s
  {
    if |s| == 0 
    then 0.0
    else f(s[0]) + sum(s[1..], f)
  }

}