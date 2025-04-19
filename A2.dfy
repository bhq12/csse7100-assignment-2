// Helper method to swap two index positions
method swap(a: array<int>, index_1: int, index_2: int)
    //Requires two valid indexes
    requires 0 <= index_1 < a.Length
    requires 0 <= index_2 < a.Length
    modifies a
    // Ensures index_1 + index_2 are swapped AND all other indexes are identical
    ensures a[index_1] == old(a[index_2])
    ensures a[index_2] == old(a[index_1])
    ensures forall i :: 0 <= i < a.Length ==> i == index_1 || i == index_2 || a[i] == old(a[i])
{
    //Swap the two positiions in the new array
    var temp_1 := a[index_1];
    var temp_2 := a[index_2];
    print "index_1: ", index_1, ", a[index_1]: ", a[index_1], ", index_2: ", index_2, "a[index_2]: ", a[index_2], "\n";
    print "a.Length: ", a.Length, "\n";
    a[index_1] := temp_2;
    a[index_2] := temp_1;
}

method recursiveSwap(a: array<int>, index_1: int, index_2: int, call_count: int)
    requires call_count <= a.Length
    requires 0 <= index_1 < a.Length
    requires a.Length >= 6
    requires 0 <= index_2 < a.Length
    modifies a
    decreases a.Length - call_count
{
    print "\nindex_1: ", index_1, ", index_2: ", index_2, "\n";
    if (call_count < a.Length && index_1 != a[index_2]) {
            //TODO: Call the swap function?
            // How do we do the requires when we are mutating the array?
            print "\n[", a[0], ",", a[1], ",", a[2], ",", a[3], ",", a[4], ",", a[5], "]\n";
            swap(a, index_1, index_2);
            if (0 <= a[index_1] < a.Length) {
                print "RECURSE\n";
                recursiveSwap(a, index_1, a[index_1],call_count+1);
            }
            
    }
}



//Q1
// Ideas: 
// For elements in a
// if a[i] < len(a) then b[a[i]] = a[i]
// else: no guarantee
// Thought: What happens if there are duplicates?
method Rearrange(a: array<int>)
requires a.Length >= 6
modifies a
ensures true
//ensures forall i :: 0 <= i < a.Length ==> i < 0 || i > a.Length || a[i] == i 
//Either the element at a[i] is not a valid index OR the element at a[i] is at the position i?
//Confused: what do we do about duplicates?
//in: [1,0,1]
//out: [0,1,1]
//a[0] == 0
//a[1] == 1
//a[2] == 1 ???
//ensures forall i :: 0 <= i < a.Length ==> a[i] < 0 || a[i] >= a.Length || a[i] == i

{
    var n: nat;
    n := 0;

    while (n < a.Length)
        invariant 0 <= n <= a.Length
        decreases a.Length - n
    {
        if (
            a[n] < a.Length
            && a.Length >= 1
            && 0 <= n < a.Length
            && 0 <= a[n] < a.Length
            ) {
            print "INCREMENT\n";
            recursiveSwap(a, n, a[n], 1);
        }
        n := n + 1;
    }



}

//Q2
method Find(a: array<int>) returns (r: int)
modifies a
requires a.Length >= 6
ensures true
{
    Rearrange(a);
    var i := 0;
    while (i < a.Length)
        invariant 0 <= i <= a.Length
        decreases a.Length - i
    {
        if (a[i] != i) {
            return i;
        }
        i := i + 1;
    }
    return i;
}

//Q4 - CSSE3100 students should delete this line and the following line
//method FindAll(a: array<int>) returns (b: array<bool>) 

method Main()
{
    var a := new int[6];
    a[0] := 2;
    a[1] := -3;
    a[2] := 4;
    a[3] := 1;
    a[4] := 1;
    a[5] := 7;
    print "REARRANGE";
    print "\n[", a[0], ",", a[1], ",", a[2], ",", a[3], ",", a[4], ",", a[5], "]\n";
    Rearrange(a);
    print "\n[", a[0], ",", a[1], ",", a[2], ",", a[3], ",", a[4], ",", a[5], "]\n";
    print "FIND";
    a[0] := 2;
    a[1] := -3;
    a[2] := 4;
    a[3] := 1;
    a[4] := 1;
    a[5] := 7;
    var result := Find(a);
    print "\nFind(a): ", result;


    print "\n";
}
