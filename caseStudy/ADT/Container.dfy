include "../../theory/math/TypeR0.dfy"

/******************************************************************************
  Container ADT
******************************************************************************/

module Container {

  import opened TypeR0

  trait {:termination false} Container<T> {

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
      requires  Valid()
      requires 0 <= i < Size()

    // Returns the set of heap objects that are part of this data structure's representation
    function Repr(): set<object>
      reads this

    // Returns true iff the data structure's invariant holds
    ghost predicate Valid()
      reads this, Repr()   

  }

}