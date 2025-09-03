include "../../../theory/math/ExpReal.dfy"
include "../../../theory/math/TypeR0.dfy"
include "../../../theory/ComplexityR0.dfy"
include "../../../theory/math/TypeR0.dfy"
include "../Container.dfy"
include "./Cost2.dfy"

/******************************************************************************
  List ADT
  An indexed collection of elements
******************************************************************************/

module Cost2List {

  import opened TypeR0
  import opened ExpReal
  import opened ComplexityR0
  import opened Container
  import opened Cost2

  trait Cost2List<T, OpType, State> {

    /******************************************************************************
      Query operations
    ******************************************************************************/

    // Returns the size of the container
    function Size(): nat
      reads this, Repr()
      // Pre:
      requires Valid()

    // Returns the element at position i in the container
    function Get(i:nat): (T, ghost R0)
      reads this, Repr()
      // Pre:
      requires Valid()
      requires 0 <= i < Size()

    // Returns the set of heap objects that are part of this data structure's representation
    function Repr(): set<object>
      reads this

    // Returns true iff the data structure's invariant holds
    ghost predicate Valid()
      reads this, Repr()   

    ghost predicate ValidModel()
      reads this, Repr()  
      requires Valid()       

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
    method Insert(k:nat, x:T) returns (ghost c:Cost2<OpType, State>)
      modifies this, Repr()    
      // Pre:
      requires Valid() && ValidModel()
      requires 0 <= k <= Size()
      requires !IsFull()
      // Post:
      ensures  Valid() && ValidModel()
      ensures  Size() == old(Size()) + 1
      ensures  forall j :: 0 <= j < k           ==> Get(j).0 == old(Get(j).0)    // [0, k)           is unchanged  
      ensures  forall j :: k < j <= old(Size()) ==> Get(j).0 == old(Get(j-1).0)  // [k, old(Size())) is right shifted  
      ensures  Get(k).0 == x                                                     // xs[k] == x

    // Appends element x in the list
    method Append(x:T) returns (ghost c:Cost2<OpType, State>)
      modifies this, Repr()    
      // Pre:
      requires Valid() && ValidModel()
      requires !IsFull()
      // Post:
      ensures  Valid() && ValidModel()
      ensures  Size() == old(Size()) + 1
      ensures  forall j :: 0 <= j < old(Size()) ==> Get(j).0 == old(Get(j).0)    // [0, old(Size())) is unchanged  
      ensures  Get(old(Size())).0 == x                                    

  }  

}