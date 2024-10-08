Read("cong.g");

S := Semigroup([ Transformation( [ 3, 6, 3, 3, 2, 8, 4, 3, 2 ] ),
                 Transformation( [ 6, 8, 2, 6, 3, 8, 3, 7, 4 ] ) ]);

ShortStringRep := function(partition)
  return List(partition, A -> Concatenation(List(A, String)));
end;

Print(List(AsSet(AllStateSetCongruences(Generators(S))), ShortStringRep));

