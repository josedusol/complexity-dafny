include "../../../theory/math/TypeR0.dfy"
include "../Container.dfy"

/******************************************************************************
  List ADT
  An indexed collection of elements
******************************************************************************/

module List {

  import opened TypeR0
  import opened Container

  trait List<T> extends Container<T> {

    /******************************************************************************
      Query operations
    ******************************************************************************/

    // Returns the capacity of the list
    function Capacity(): nat
      reads this, Repr()
      // Pre:
      requires Valid()    

    // Returns true iff the list is full
    predicate IsFull()
      reads this, Repr()
      // Pre:
      requires Valid()  
    {
      Size() == Capacity()
    }       

    /******************************************************************************
      Update operations
    ******************************************************************************/

    // Inserts element x at position k in the list
    method Insert(k:nat, x:T) returns (ghost t:R0)
      modifies this, Repr()    
      // Pre:
      requires Valid()
      requires 0 <= k <= Size()
      requires !IsFull()
      // Post:
      ensures  Valid()
      ensures  Size() == old(Size()) + 1
      ensures  forall j :: 0 <= j < k           ==> Get(j).0 == old(Get(j).0)    // [0, k)           is unchanged  
      ensures  forall j :: k < j <= old(Size()) ==> Get(j).0 == old(Get(j-1).0)  // [k, old(Size())) is right shifted  
      ensures  Get(k).0 == x                                                     // xs[k] == x

    // Appends element x in the list
    method Append(x:T) returns (ghost t:R0)
      modifies this, Repr()    
      // Pre:
      requires Valid()
      requires !IsFull()
      // Post:
      ensures  Valid()
      ensures  Size() == old(Size()) + 1
      ensures  forall j :: 0 <= j < old(Size()) ==> Get(j).0 == old(Get(j).0)    // [0, old(Size())) is unchanged  
      ensures  Get(old(Size())).0 == x                                    

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