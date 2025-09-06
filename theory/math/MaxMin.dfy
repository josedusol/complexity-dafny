/******************************************************************************
  Maximum and minimum
******************************************************************************/

module MaxMin {

  function max(a:int, b:int) : int
  {
    if a < b then b else a
  }

  function min(a:int, b:int): int
  {
    if a < b then a else b
  }

  // n >= 0 ==> max(0,n) = n
  lemma lem_max_leftId(n:int)
    requires n >= 0
    ensures max(0, n) == n 
  {}

  // n >= 0 ==> max(0,n) = n
  lemma lem_max_rightId(n:int) 
    requires n >= 0
    ensures max(n, 0) == n
  {}

}