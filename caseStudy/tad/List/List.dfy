/******************************************************************************
  List ADT
******************************************************************************/

abstract module List {

  /******************************************************************************
    Container: a collection of elements
  ******************************************************************************/

  trait Container<T> {
    /******************************************************************************
      Query operations
    ******************************************************************************/

    // Returns the size of the container
    function Size(): nat
    //function Size(): (r:nat, ghost proof:bool)
      reads this
      requires Valid()

    // Returns the element at position i in the container
    function Get(i:nat): (T, ghost nat)
      reads this, Repr()
      requires Valid()
      requires i < Size()

    // Returns the set of objects that are part of the data structure's representation
    function Repr(): set<object>
      reads this
      requires Valid()

    // Returns true iff the data structure's invariant holds
    predicate Valid()
      reads this   
  }

  /******************************************************************************
    List: an indexed collection of elements without dynamic size constraints
  ******************************************************************************/

  trait List<T> extends Container<T> {
    /******************************************************************************
      Query operations
    ******************************************************************************/

    // Same as Container

    /******************************************************************************
      Update operations
    ******************************************************************************/

    // Inserts element x at position i in the list
    method Insert(i:nat, x:T) returns (ghost t:nat)
      modifies this    
      // pre
      requires Valid()
      requires 0 <= i <= Size()
      // post
      ensures  Valid()
      ensures  Size() == old(Size()) + 1
      ensures  forall j :: 0 <= j < i ==> Get(j) == old(Get(j))
      ensures  Get(i).0 == x
      ensures  forall j :: i < j < Size() ==> Get(j) == old(Get(j-1))

    // Deletes element at position i in the list
    method Delete(i:nat) returns (ghost t:nat)
      modifies this    
      // pre
      requires Valid()
      requires 0 <= i < Size()
      // post
      ensures  Valid()
      ensures  Size() == old(Size()) - 1
      ensures  forall j :: 0 <= j < i ==> Get(j) == old(Get(j))
      ensures  forall j :: i <= j < Size() ==> Get(j) == old(Get(j+1))
  }

  /******************************************************************************
    FixedList: an indexed collection of elements with fixed capacity
  ******************************************************************************/

  trait FixedList<T> extends Container<T> {
    /******************************************************************************
      Query operations
    ******************************************************************************/

    // Returns true iff the list is full
    predicate Full()
      reads this
      requires Valid()

    // Returns the size of the container
    // function Size2(): (int, ghost int)
    // //function Size(): (r:nat, ghost proof:bool)
    //   reads this
    //   requires Valid()      

    /******************************************************************************
      Update operations
    ******************************************************************************/

    // Inserts element x at position i in the list
    method Insert(i:nat, x:T) returns (ghost t:nat)
      modifies this    
      // pre
      requires Valid()
      requires 0 <= i <= Size()
      requires !Full()
      // post
      ensures  Valid()
      ensures  Size() == old(Size()) + 1
      ensures  forall j :: 0 <= j < i ==> Get(j) == old(Get(j))
      ensures  Get(i).0 == x
      ensures  forall j :: i < j < Size() ==> Get(j) == old(Get(j-1))

    // Deletes element at position i in the list
    method Delete(i:nat) returns (ghost t:nat)
      modifies this    
      // pre
      requires Valid()
      requires 0 <= i < Size()
      // post
      ensures  Valid()
      ensures  Size() == old(Size()) - 1
      ensures  forall j :: 0 <= j < i ==> Get(j) == old(Get(j))
      ensures  forall j :: i <= j < Size() ==> Get(j) == old(Get(j+1))
  }  

}