// Helper method to swap two index positions
method swap(a: array<int>, index_1: int, index_2: int) returns (b: array<int>)
    //Requires two valid indexes
    requires index_1 >= 0 && index_2 >= 0
    && index_1 < a.Length && index_2 < a.Length
    // Ensures index_1 + index_2 are swapped AND all other indexes are identical
    ensures a.Length == b.Length
    && a[index_1] == b[index_2]
    && a[index_2] == b[index_1]
    && forall i :: 0 <= i < a.Length ==> i == index_1 || i == index_2 || a[i] == b[i]
{
    //Create a copy of the array
    b := new int[a.Length];
    var i := 0;
    while (i < a.Length)
        invariant i <= a.Length
        invariant forall j :: 0 <= j < i ==> a[j] == b[j]
        decreases a.Length - i
    {
        b[i] := a[i];
        i:= i + 1;
    }
    //Swap the two positiions in the new array
    var temp_1 := a[index_1];
    var temp_2 := a[index_2];
    b[index_1] := temp_2;
    b[index_2] := temp_1;
}



//Q1
// Ideas: 
// For elements in a
// if a[i] < len(a) then b[a[i]] = a[i]
// else: no guarantee
// Thought: What happens if there are duplicates?
method Rearrange(a: array<int>)
requires true
//ensures forall i :: 0 <= i < a.Length ==> i < 0 || i > a.Length || a[i] == i 
//Either the element at a[i] is not a valid index OR the element at a[i] is at the position i?
//Confused: what do we do about duplicates?
//in: [1,0,1]
//out: [0,1,1]
//a[0] == 0
//a[1] == 1
//a[2] == 1 ???
ensures forall i :: 0 <= i < a.Length ==> a[i] < 0 || a[i] >= a.Length || a[i] == i

{
    var n: nat;
    n := 0;

    while (n < a.Length)
        invariant 0 <= n <= a.Length
        decreases a.Length - n
    {
        while 
        n := n + 1;
    }



}

//Q2
method Find(a: array<int>) returns (r: int)

//Q4 - CSSE3100 students should delete this line and the following line
method FindAll(a: array<int>) returns (b: array<bool>) 