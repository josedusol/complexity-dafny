
/**************************************************************************
  A functionally correct linear search algorithm
**************************************************************************/

// Postcondition
ghost predicate post<A>(s:seq<A>, x:A, i:nat)
{
     (0 <= i < |s| ==> s[i] == x)
  && (i == |s|     ==> (forall j :: 0 <= j < |s| ==> s[j] != x))
}

// Invariant
ghost predicate inv<A>(s:seq<A>, x:A, i:nat, n:nat)
{
     0 <= i <= n && n <= |s|
  && (0 <= n < |s| ==> s[i] == x)      
  && (n == |s|     ==> (forall j :: 0 <= j < i ==> s[j] != x))
}

method linearSearch<A(==)>(s:seq<A>, x:A) returns (i:nat)
  ensures post(s, x, i)
{
  var n:nat;
  i, n := 0, |s|;
  while i != n
    invariant inv(s, x, i, n)
    decreases n - i
  {
    if s[i] != x {
      i := i+1 ;     
    } else {
      n := i;  // break;
    }
  }
} 

// a more consize alternative
method linearSearch2<A(==)>(s:seq<A>, x:A) returns (i:nat)
  ensures post(s, x, i)
{
  var n:nat;
  i, n := 0, |s|;
  while i != n && s[i] != x
    invariant inv(s, x, i, n)
    decreases n - i
  {
    i := i + 1;
  }
} 
