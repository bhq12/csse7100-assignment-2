// Helper method to swap two index positions
//method swap(a: array<int>, index_1: int, index_2: int)
//    // Ensures index_1 + index_2 are swapped AND all other indexes are identical
//    ensures a[index_1] == old(a[index_2])
//    ensures a[index_2] == old(a[index_1])
//    ensures forall i :: 0 <= i < a.Length ==> i == index_1 || i == index_2 || a[i] == old(a[i])


//Q1
// Ideas: 
// For elements in a
// if a[i] < len(a) then b[a[i]] = a[i]
// else: no guarantee
// Thought: What happens if there are duplicates?
method Rearrange(a: array<int>)
modifies a
ensures true
//ensures forall i :: 0 <= i < a.Length ==> a[i] < 0 || a.Length <= a[i] || a[a[i]] == a[i]
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
                var index_1 := n;
                var index_2 := a[n];
                var swap_count := 0;

                while (
                    0 <= index_1 < a.Length
                    && 0 <= index_2 < a.Length
                    && swap_count < a.Length
                    //&& a[] != index_2
                )
                    decreases a.Length - swap_count
                {
                    var temp_1 := a[index_1];
                    var temp_2 := a[index_2];
                    print "index_1: ", index_1, ", a[index_1]: ", a[index_1], ", index_2: ", index_2, "a[index_2]: ", a[index_2], "\n"; print "a.Length: ", a.Length, "\n";
                    a[index_1] := temp_2;
                    a[index_2] := temp_1;

                    index_2 := a[index_1];
                    swap_count := swap_count + 1;
                }



            print "INCREMENT\n";
            //recursiveSwap(a, n, a[n], 1);
        }
        n := n + 1;
    }



}

//Q2
method Find(a: array<int>) returns (r: int)
modifies a
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
method FindAll(a: array<int>) returns (b: array<bool>)
    modifies a
{
    b := new bool[a.Length];

    var i := 0;

    Rearrange(a);

    while (i < a.Length)
        invariant 0 <= i <= a.Length
        decreases a.Length - i
        {
            if (a[i] == i) {
                b[i] := true;
            } else {
                b[i] := false;
            }
            
            i := i + 1;
        }


}

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
    //print "FIND";
    //a[0] := 2;
    //a[1] := -3;
    //a[2] := 4;
    //a[3] := 1;
    //a[4] := 1;
    //a[5] := 7;
    //var result := Find(a);
    //print "\nFind(a): ", result;

    //print "FINDALL";
    //a[0] := 2;
    //a[1] := -3;
    //a[2] := 4;
    //a[3] := 1;
    //a[4] := 1;
    //a[5] := 7;
    //var b := FindAll(a);
    //if (b.Length > 5){
    //    print "\n[", b[0], ",", b[1], ",", b[2], ",", b[3], ",", b[4], ",", b[5], "]\n";
    //}
    //print "\n";


}
