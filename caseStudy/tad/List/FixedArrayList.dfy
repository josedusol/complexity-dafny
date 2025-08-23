include "./List.dfy"
include "../../../theory/math/TypeR0.dfy"
include "../../../theory/ComplexityR0.dfy"

/******************************************************************************
  Fixed capacity array implementation of a Fixed List
******************************************************************************/

module FixedArrayList refines List {

  import opened TypeR0
  import opened ComplexityR0

  class FixedArrayList<T(0)> extends FixedList<T> {
    var xs:array<T>
    var n:nat

    constructor(capacity:nat)
      // pre
      requires capacity > 0
      // post      
      ensures Valid()
      ensures xs.Length == capacity
      ensures Size() == 0
    {
      xs := new T[capacity];  
      n := 0; 
    }   

    /******************************************************************************
      Query operations
    ******************************************************************************/

    // Returns the size of the list
    function Size(): nat
      reads this
      requires Valid()
    {
      n
    }

    // Returns the element at position i in the list
    function Get(i:nat): (ret: (T, ghost nat))    
      reads this, Repr()
      requires Valid()
      requires i < Size() 
      // complexity
      ensures var t := ret.1; t == 1
      ensures var t := ret.1; tIsBigTh(Size(), t as R0, constGrowth())      
    {
      //ghost var t := 0;
      (xs[i], ghost 1) 
    }

    // Returns the set of objects that are part of the data structure's representation
    function Repr(): set<object>
      reads this
      requires Valid()
    {
      {xs}
    }    

    // Returns true iff the data structure's invariant holds
    predicate Valid()
      reads this
    {
      && xs != null
      && 0 <= n <= xs.Length 
    }    

    // Returns true iff the array is full
    predicate Full()
      reads this
      requires Valid()
    {
      n == xs.Length
    }    

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
      // complexity
      ensures  t <= Size() 
      ensures  tIsBigTh(Size(), t as R0, linGrowth())
    {
      t := 0;
      // implementation with array shift here
    }

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
      // complexity
      ensures  t <= Size() 
      ensures  tIsBigTh(Size(), t as R0, linGrowth())       
    {
      t := 0;
      // implementation with array shift here
    }
  }

}