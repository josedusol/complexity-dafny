include "../../../theory/math/ExpReal.dfy"
include "../../../theory/math/TypeR0.dfy"
include "../../../theory/Complexity/Asymptotics.dfy"
include "../../../theory/math/TypeR0.dfy"
include "../Container.dfy"
include "./Cost.dfy"

/******************************************************************************
  List ADT
  An indexed collection of elements
******************************************************************************/

module CostList {

  import opened TypeR0
  import opened ExpReal
  import opened Asymptotics
  import opened Container
  import opened Cost

  // Abstract input type for each relevant operation
  type InsertIn<T>
  type AppendIn<T>
  type OkIn<T>

  trait CostList<T> extends Container<T> {

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
                
    method Insert_CostTest(k:nat, x:T) returns (ghost c:Cost<InsertIn<T>>)  
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

    method Append_CostTest(x:T) returns (ghost c:Cost<AppendIn<T>>)  
      modifies this, Repr()    
      // Pre:
      requires Valid()
      requires !IsFull()
      // Post:
      ensures  Valid()
      ensures  Size() == old(Size()) + 1
      ensures  forall j :: 0 <= j < old(Size()) ==> Get(j).0 == old(Get(j).0)    // [0, old(Size())) is unchanged  
      ensures  Get(old(Size())).0 == x     

    method OK_CostTest() returns (ghost c:Cost<OkIn<T>>)  
      modifies this, Repr()    
      // Pre:
      requires Valid()
      // Post:
      ensures  Valid()     
      ensures  tIsBigOh(c.Size(), c.Count() as R0, linGrowth())     
  }  

}