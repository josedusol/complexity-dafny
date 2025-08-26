include "../../../theory/math/TypeR0.dfy"
include "../Container.dfy"

/******************************************************************************
  DynamicList ADT
  An indexed collection of elements without size constraints
******************************************************************************/

module DynamicList {

  import opened TypeR0
  import opened Container

  trait DynamicList<T> extends Container<T> {

    /******************************************************************************
      Query operations
    ******************************************************************************/

    // Same as Container

    /******************************************************************************
      Update operations
    ******************************************************************************/

    // Inserts element x at position k in the list
    method Insert(k:nat, x:T) returns (ghost t:R0)
      modifies this, Repr()   
      // Pre:
      requires Valid()
      requires 0 <= k <= Size()
      // Post:
      ensures  Valid()
      ensures  Size() == old(Size()) + 1
      ensures  forall j :: 0 <= j < k           ==> Get(j).0 == old(Get(j).0)    // [0, k) is unchanged  
      ensures  forall j :: k < j <= old(Size()) ==> Get(j).0 == old(Get(j-1).0)  // (k, n] is right shifted 
      ensures  Get(k).0 == x                                                     // xs[k] == x

    // Deletes element at position k in the list
    method Delete(k:nat) returns (ghost t:R0)
      modifies this, Repr()    
      // Pre:
      requires Valid()
      requires 0 <= k < Size()
      // Post:
      ensures  Valid()
      ensures  Size() == old(Size()) - 1
      ensures  forall j :: 0 <= j < k      ==> Get(j).0 == old(Get(j).0)
      ensures  forall j :: k <= j < Size() ==> Get(j).0 == old(Get(j+1).0)

  } 

}