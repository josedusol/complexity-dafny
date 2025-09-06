include "../../../theory/math/ExpReal.dfy"
include "../../../theory/math/TypeR0.dfy"
include "../../../theory/ComplexityR0.dfy"
include "./Cost2List.dfy"

/******************************************************************************
  ArrayList ADT
******************************************************************************/

module Cost2ArrayList refines Cost2List {

  datatype ArrayOp<T> = Write(i: nat, v: T)  // | Shift(from: nat, to: nat)

  type State<T> = seq<T>

  trait Cost2ArrayList<T(0)> extends Cost2List<T, ArrayOp<T>, State<T>> {

    ghost var elems:seq<T>  // ghost model for physical array arr

    /******************************************************************************
      Query operations
    ******************************************************************************/

    // Returns true iff the model is consistent with the data
    ghost predicate ValidModel()
      reads this, Repr()
      requires Valid()      
    {
      && Size() == |elems| 
      && (forall i :: 0 <= i < Size() ==> Get(i).0 == elems[i])
    }    
    
    /******************************************************************************
      Update operations
    ******************************************************************************/
    
    //Experiment with cost objects

    // Inserts element x at position k in the list
    method Insert(k:nat, x:T) returns (ghost c:Cost2<ArrayOp<T>, State<T>>)
      modifies this, Repr()  
      // Pre:
      requires Valid() && ValidModel()
      requires 0 <= k <= Size()
      requires !IsFull()
      // Post:
      ensures  Valid() && ValidModel() && fresh(Repr() - old(Repr()))
      ensures  Size() == old(Size()) + 1
      ensures  forall j :: 0 <= j < k           ==> Get(j).0 == old(Get(j).0)    // [0, k)           is unchanged  
      ensures  forall j :: k < j <= old(Size()) ==> Get(j).0 == old(Get(j-1).0)  // [k, old(Size())) is right shifted 
      ensures  Get(k).0 == x                                                     // xs[k] == x
      // Cost:
      ensures  c.OpsValid(old(elems))            
      ensures  c.ApplyOps(old(elems)) == elems    // Even this does not prevent under-reporting of cost.
      ensures  c.Count() == old(Size()) - k + 1

    method Append(x:T) returns (ghost c:Cost2<ArrayOp<T>, State<T>>)  
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

  /***********************************************/

  class {:ghost} ArrayInsertCost<T> extends Cost2<ArrayOp<T>, seq<T>> {

    ghost constructor()
      ensures ops == []
    { 
      ops := []; 
      totalCost := 0;
    }

    ghost predicate OpsValid(init:seq<T>)
      reads this
    {
      true // TODO
    }

    ghost function ApplyOps(init:seq<T>): seq<T>
      reads this
      requires OpsValid(init)
    {
      init  // TODO
    }

  }

}