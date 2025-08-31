include "../../../../theory/math/ExpReal.dfy"
include "../../../../theory/math/LemFunction.dfy"
include "../../../../theory/math/TypeR0.dfy"
include "../../../../theory/ComplexityR0.dfy"
include "../DynaList.dfy"
include "./LemDynaArrayList.dfy"

/******************************************************************************
  Dynamic Array implementation of a List
******************************************************************************/

module DynaArrayList refines DynaList {

  import opened ExpReal
  import opened LemFunction
  import opened ComplexityR0
  import opened LemDynaArrayList

  class DynaArrayList<T(0)> extends DynaList<T> {

    var arr:array<T>
    var nElems:nat
    var m:nat
    ghost var elems:seq<T>  // ghost model for physical array arr

    constructor(capacity:nat, gfactor:nat)
      // Pre:
      requires capacity > 0
      requires gfactor > 1
      // Post:      
      ensures Valid()
      ensures Size() == 0
      ensures arr.Length == capacity
      ensures m == gfactor
    {
      arr := new T[capacity];  
      nElems := 0; 
      m := gfactor;
      elems := [];
    }   

    // default constructor
    static method Create<T(0)>() returns (obj:DynaArrayList)
      ensures obj.arr.Length == 1 && obj.m == 2
    {
      obj := new DynaArrayList<T>(1, 2);
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
      && m > 1
      && this in Repr() 
      && arr  in Repr()
      // The array and its ghost counterpart are aligned
      && nElems == |elems| 
      && (forall i :: 0 <= i < nElems ==> arr[i] == elems[i])
    }   

    /******************************************************************************
      Update operations
    ******************************************************************************/

    // Set growth factor m > 1
    method SetGrowthFactor(gfactor:nat)
      modifies this, Repr()
      // Pre: 
      requires Valid()
      requires gfactor > 1
      // Post: 
      ensures Valid()
      ensures m == gfactor
    {
      m := gfactor;
    }

    // Increment array capacity by growth factor
    method Grow() returns (ghost t:R0) 
      modifies this, Repr()
      // Pre: 
      requires Valid()
      // Post:
      ensures Valid() && fresh(Repr() - old(Repr()))
      ensures !IsFull()
      ensures arr.Length == m*old(arr.Length) > old(arr.Length)
      ensures arr[..nElems] == old(arr[..nElems])
      ensures m == old(m)
      // Complexity:
      ensures var N := old(arr.Length); && t == Tgrow(m,N,Size())
                                        && t <= Tgrow(m,N,N)
                                        && tIsBigO(N, t as R0, linGrowth())      
    {   
      var N, m := arr.Length, m;

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
      ensures m == old(m)
      // Complexity:
      ensures  var N := old(Size()); && t <= Tinsert(m,N,k)
                                     && tIsBigO(N, t as R0, linGrowth())
      ensures  var N := old(Size()); !old(IsFull()) ==> t == Tinsert2(N,k)                            
    {
      var N, m := Size(), m;
      t := 0.0;

      // Grow array if neccesary
      if IsFull() { 
        assert N == arr.Length;
        t := Grow(); 
        assert t == Tgrow(m,N,N) == ((m+1)*N) as R0; 
        assert !IsFull();
        assert N < arr.Length;   
      }
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
        invariant t == if old(IsFull()) then ((m+1)*N + N - i) as R0 else (N - i) as R0
        decreases i
      {
        arr[i] := arr[i-1]; // shift right
        assert arr[i] == old(arr[i-1]);
        i := i - 1;
        t := t + 1.0;
      }
      assert i == k;
      assert arr[..k] == old(arr[..k]) == elems[..k];          // [0, k) is unchanged
      assert arr[k+1..N+1] == old(arr[k..N]) == elems[k+1..];  // (k, N] is right shifted 
      assert t == if old(IsFull()) then ((m+1)*N + N - k) as R0 else (N - k) as R0;

      // 2. Insert x at position k
      arr[k] := x;
      t := t + 1.0;
    
      // Update number of elements
      nElems := nElems + 1;
      assert forall j :: 0 <= j < |elems| ==> arr[j] == elems[j];

      if old(IsFull()) {
        calc {
             t; 
          == ((m+1)*N + N - k + 1) as R0;
          == ((m+2)*N - k + 1) as R0;
          == Tinsert(m, N, k);
          <= TinsertUp(m, N);
        }      
        assert (N => TinsertUp(m,N)) in O(linGrowth()) by { var c, n0 := lem_Insert_TinsertBigOlin(m); }  
      } else {
        calc {
             t; 
          == (N - k + 1) as R0;
          == Tinsert2(N, k);
          <= Tinsert2Up(N);
        }        
        assert Tinsert2Up in O(linGrowth()) by { var c, n0 := lem_Insert_Tinsert2BigOlin(); }
      }
    }

    // Appends element x in the list
    method Append(x:T) returns (ghost t:R0)
      modifies this, Repr()    
      // Pre:
      requires Valid()
      // Post:
      ensures  Valid()
      ensures  Size() == old(Size()) + 1
      ensures  forall j :: 0 <= j < old(Size()) ==> Get(j).0 == old(Get(j).0)    // [0, old(Size())) is unchanged  
      ensures  Get(old(Size())).0 == x   
      ensures m == old(m)
      // Complexity:
      ensures  var N := old(Size()); && t <= Tappend(m, N)
                                     && tIsBigO(N, t as R0, linGrowth())  
      ensures  var N := old(Size()); !old(IsFull()) ==> && t == Tappend2(N)    
                                                        && tIsBigO(N, t as R0, constGrowth())                                   
    {
      var N, m := Size(), m;
      t := Insert(N, x);

      if old(IsFull()) {
        assert t <= Tinsert(m,N,N) == ((m+1)*N + 1) as R0; 
        assert (N => Tappend(m,N)) in O(linGrowth()) by { var c, n0 := lem_Append_TappendBigOlin(m); }    
      } else {
        assert t == Tinsert2(N,N) == (N - N + 1) as R0 == 1.0; 
        assert Tappend2 in O(constGrowth()) by { var c, n0 := lem_Append_Tappend2BigOconst(); }    
      }
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