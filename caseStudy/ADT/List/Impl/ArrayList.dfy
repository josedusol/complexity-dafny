include "../../../../theory/math/ExpReal.dfy"
include "../../../../theory/math/TypeR0.dfy"
include "../../../../theory/ComplexityR0.dfy"
include "../List.dfy"
include "./LemArrayList.dfy"

/******************************************************************************
  Array implementation of a List
******************************************************************************/

module ArrayList refines List {

  import opened LemArrayList

  class ArrayList<T(0)> extends List<T> {

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

    // default constructor
    static method Create<T(0)>() returns (obj:ArrayList)
      ensures obj.arr.Length == 1
    {
      obj := new ArrayList<T>(1);
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

    // Returns the capacity of the list
    function Capacity(): nat
      reads this, Repr()
      // Pre:
      requires Valid()  
    {
      arr.Length
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
      ensures  Valid() && fresh(Repr() - old(Repr()))
      ensures  Size() == old(Size()) + 1
      ensures  forall j :: 0 <= j < k           ==> Get(j).0 == old(Get(j).0)    // [0, k)           is unchanged  
      ensures  forall j :: k < j <= old(Size()) ==> Get(j).0 == old(Get(j-1).0)  // [k, old(Size())) is right shifted 
      ensures  Get(k).0 == x                                                     // xs[k] == x
      // Complexity:
      ensures  var N := old(Size()); && t == Tinsert(N,k)
                                     && tIsBigO(N, t as R0, linGrowth())                             
    {
      var N := Size();
      t := 0.0;

      // Update model
      elems := elems[..k] + [x] + elems[k..];
      
      // Update array:
      // 1. Shift [k, N) to the right
      for i := N downto k
        modifies arr
        invariant N < arr.Length
        invariant arr[..i]      == old(arr[..i])   // [0, i) is unchanged  
        invariant arr[i+1..N+1] == old(arr[i..N])  // (i, N) is right shifted        
        invariant t == (N - i) as R0    
      {
        arr[i+1] := arr[i]; // shift right
        assert arr[i+1] == old(arr[i]);
        t := t + 1.0;
      }
      assert arr[..k] == old(arr[..k]) == elems[..k];          // [0, k) is unchanged
      assert arr[k+1..N+1] == old(arr[k..N]) == elems[k+1..];  // [k, N] is right shifted 

      // 2. Insert x at position k
      arr[k] := x;
      t := t + 1.0;

      // Update number of elements
      nElems := nElems + 1;
      assert forall j :: 0 <= j < |elems| ==> arr[j] == elems[j];

      assert t == (N - k + 1) as R0 == Tinsert(N, k) 
               <= (N + 1) as R0     == Tinsert2(N);
      assert Tinsert2 in O(linGrowth()) by { var c, n0 := lem_Insert_Tinsert2BigOlin(); }      
    }
                                              
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
      // Complexity:
      ensures  var N := old(Size()); && t == Tappend(N) 
                                     && tIsBigO(N, t as R0, constGrowth())      
    {
      var N := Size();
      t := Insert(N, x);
      assert t == Tinsert(N, N) == 1 as R0; 
      assert Tappend in O(constGrowth()) by { var c, n0 := lem_Append_TappendBigOconst(); }      
    }

    // Deletes element at position k in the list
    method Delete(k:nat) returns (ghost t:R0)
      modifies this, Repr()
      // Pre:    
      requires Valid()
      requires 0 <= k < Size()
      // Post:
      ensures  Valid()
      ensures  Size() == old(Size()) - 1
      ensures  forall j :: 0 <= j < k      ==> Get(j).0 == old(Get(j).0)    // [0, k) is unchanged
      ensures  forall j :: k <= j < Size() ==> Get(j).0 == old(Get(j+1).0)  // (k, old(Size())) is left shifted  
      // Complexity:
      ensures  var N := old(Size()); && t == Tdelete(N, k)
                                     && tIsBigO(N, t as R0, linGrowth())       
    {
      var N := Size();
      t := 0.0;

      // Update model
      elems := elems[..k] + elems[k+1..];

      // Update array:
      // Shift elements from (k, N) to the left
      for i := k to N-1 
        modifies arr
        invariant arr[..k]  == old(arr[..k])        // [0, k) is unchanged
        invariant arr[k..i] == old(arr[k+1..i+1])   // (k, i] is left shifted
        invariant arr[i..]  == old(arr[i..])        // [i, N) still equals old
        invariant t == (i - k) as R0
      {
        arr[i] := arr[i+1]; //shift left
        t := t + 1.0;
      }
      assert arr[..k]    == old(arr[..k]) == elems[..k];     // [0, k) is unchanged
      assert arr[k..N-1] == old(arr[k+1..N]) == elems[k..];  // (k, N) is left shifted

      // Update number of elements
      nElems := nElems - 1;
      assert forall j :: 0 <= j < |elems| ==> arr[j] == elems[j];

      assert t == (N - k - 1) as R0 == Tdelete(N, k) 
               <= N as R0           == Tdelete2(N);
      assert Tdelete2 in O(linGrowth()) by { var c, n0 := lem_Delete_Tdelete2BigOlin(); }          
    }

  }

}