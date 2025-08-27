include "../../../../theory/math/ExpReal.dfy"
include "../../../../theory/math/TypeR0.dfy"
include "../../../../theory/ComplexityR0.dfy"
include "../DynaList.dfy"
include "./LemDynaArrayList.dfy"

/******************************************************************************
  Dynamic Array implementation of a List
******************************************************************************/

module DynaArrayList refines DynaList {

  import opened ExpReal
  import opened ComplexityR0
  import opened LemDynaArrayList

  class DynaArrayList<T(0)> extends DynaList<T> {

    var arr:array<T>
    var nElems:nat
    ghost var elems:seq<T>  // ghost model for physical array arr

    constructor(capacity:nat)
      // Pre:
      requires capacity > 0
      // Post:      
      ensures Valid()
      ensures arr.Length == capacity
      ensures Size() == 0
    {
      arr := new T[capacity];  
      nElems := 0; 
      elems := [];
    }   

    /******************************************************************************
      Query operations
    ******************************************************************************/

    // Returns the size of the list
    function Size(): nat
      reads this, Repr()
      // Pre:
      requires Valid()
    {
      nElems
    }

    // Returns the element at position i in the list
    function Get(i:nat): (ret: (T, ghost R0))    
      reads this, Repr()
      // Pre:
      requires Valid()
      requires 0 <= i < Size() 
      // Complexity:
      ensures var t := ret.1; t <= Tget(Size())
      ensures var t := ret.1; tIsBigO(Size(), t as R0, constGrowth())      
    {
      lem_Get_TgetBigOconst();
      (arr[i], ghost 1.0)
    }

    // Returns the set of heap objects that are part of this data structure's representation
    function Repr(): set<object>
      reads this
    {
      {this, arr}
    }    

    // Returns true iff the data structure's invariant holds
    ghost predicate Valid()
      reads this, Repr()
    {
      && 0 <= nElems <= arr.Length
      && 0 < arr.Length
      && this in Repr() 
      && arr  in Repr()
      // The array and its ghost counterpart are aligned
      && nElems == |elems| 
      && (forall i :: 0 <= i < nElems ==> arr[i] == elems[i])
    }    

    // Returns true iff the array is full
    predicate IsFull()
      reads this, Repr()
      // Pre:
      requires Valid()
    {
      nElems == arr.Length
    }        

    /******************************************************************************
      Update operations
    ******************************************************************************/

    // Increment array capacity by a multiplicative factor m > 1
    method Grow(m:nat) returns (ghost t:R0) 
      modifies this, Repr()
      // Pre: 
      requires Valid()
      requires m > 1
      // Post:
      ensures Valid() && fresh(Repr() - old(Repr()))
      ensures !IsFull()
      ensures arr.Length == m*old(arr.Length) > old(arr.Length)
      ensures arr[..nElems] == old(arr[..nElems])
      // Complexity:
      ensures  var N := old(arr.Length); && t == Tgrow(m,N,Size())
                                         && t <= Tgrow(m,N,N)
                                         && tIsBigO(N, t as R0, linGrowth())      
    {   
      var N := arr.Length;

      // Allocate new array
      var newArr := new T[m*N];
      t := (m*N) as R0;
      
      // Copy old array content to new array
      forall i | 0 <= i < Size() { 
        newArr[i] := arr[i]; 
      }
      t := t + Size() as R0;

      // Update current array
      arr := newArr;
      assert forall j :: 0 <= j < |elems| ==> arr[j] == elems[j];
    
      assert t == (m*N + Size()) as R0 == Tgrow(m,N,Size()) <= Tgrow(m,N,N);
      assert (N => Tgrow(m,N,N)) in O(linGrowth()) by { var c, n0 := lem_Grow_TgrowBigOlin(m); }    
    }

    // Inserts element x at position k in the list
    method Insert(k:nat, x:T) returns (ghost t:R0)
      modifies this, Repr()    
      // Pre:      
      requires Valid()
      requires 0 <= k <= Size()
      // Post:      
      ensures  Valid() && fresh(Repr() - old(Repr()))
      ensures  Size() == old(Size()) + 1
      ensures  forall j :: 0 <= j < k           ==> Get(j).0 == old(Get(j).0)    // [0, k)           is unchanged  
      ensures  forall j :: k < j <= old(Size()) ==> Get(j).0 == old(Get(j-1).0)  // (k, old(Size())] is right shifted 
      ensures  Get(k).0 == x                                                     // xs[k] == x
      // Complexity:
      ensures  var N := old(Size()); && t <= Tinsert(N,k) 
                                     && t <= Tinsert2(N) 
                                     && tIsBigO(N, t as R0, linGrowth())
    {
      var N := Size();
      t := 0.0;

      // Double array size if neccesary
      if IsFull() { 
        assert nElems == N == arr.Length;
        t := Grow(2); 
        assert t == Tgrow(2,N,N) == (3*N) as R0; 
      }
      assert !IsFull();
      assert N < arr.Length;
      assert t <= (3*N) as R0; 
      assert arr[..N] == elems;

      // Update model
      elems := elems[..k] + [x] + elems[k..];

      // Update array:
      // 1. Shift (k, N] to the right
      var i := N;
      while i > k
        modifies arr
        invariant k <= i <= N < arr.Length    
        invariant arr[..i]      == old(arr[..i])   // [0, i) is unchanged  
        invariant arr[i+1..N+1] == old(arr[i..N])  // (i, N] is right shifted      
        invariant t <= (3*N + N - i) as R0
        decreases i
      {
        arr[i] := arr[i-1]; // shift right
        i := i - 1;
        t := t + 1.0;
      }
      assert arr[k+1..N+1] == old(arr[k..N]);  // (k, N] is right shifted 
      assert old(arr[k..N]) == elems[k+1..];

      // 2. Insert x at position k
      assert i == k;
      arr[k] := x;
      assert arr[..k] == old(arr[..k]);  // [0, k) is unchanged
    
      // Update number of elements
      nElems := nElems + 1;

      assert t <= (4*N - k) as R0 == Tinsert(N, k)
               <= (4*N) as R0     == Tinsert2(N);
      assert Tinsert2 in O(linGrowth()) by { var c, n0 := lem_Insert_Tinsert2BigOlin(k); }            
    }

    // Deletes element at position k in the list
    method {:axiom} Delete(k:nat) returns (ghost t:R0)
      modifies this, Repr()
      // Pre:    
      requires Valid()
      requires 0 <= k < Size()
      // Post:
      ensures  Valid() && fresh(Repr() - old(Repr()))
      ensures  Size() == old(Size()) - 1
      ensures  forall j :: 0 <= j < k      ==> Get(j).0 == old(Get(j).0)
      ensures  forall j :: k <= j < Size() ==> Get(j).0 == old(Get(j+1).0)   
      // Complexity:
      ensures  var N := old(Size()); && t <= Tdelete(N)
                                     && tIsBigO(N, t as R0, linGrowth())       
      // TODO: implementation with array shift here

  }

}