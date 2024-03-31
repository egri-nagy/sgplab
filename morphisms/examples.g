Read("morphisms.g");

### EXAMPLE 1 a minimal meaningful example of a surjective morphism
# joining two states with a transposition
ex1S := Semigroup(Transformation([1,3,2]), #transposition of 2 and 3
                  Transformation([1,1,1]),
                  Transformation([2,2,2]));

#collapsing 2 and 3
ex1theta := HashMap([[1,[1]],
                     [2,[2]],
                     [3,[2]]]);

ex1phi := HashMap([[Transformation([1,2,3]), [Transformation([1,2])]],
                   [Transformation([1,1,1]), [Transformation([1,1])]],
                   [Transformation([2,2,2]), [Transformation([2,2])]],
                   [Transformation([3,3,3]), [Transformation([2,2])]],
                   [Transformation([1,3,2]), [Transformation([1,2])]]]);

if IsRelationalMorphism(ex1theta, ex1phi, OnPoints, OnPoints) then
  Display("Example 1 OK");
else
  Error("Example 1");
fi;

### EXAMPLE 2 not a relational morphism
ex2theta := HashMap([[1,[1]],
                     [2,[2]]]);

ex2phi := HashMap([[Transformation([1,2]), [Transformation([1,2])]],
                   [Transformation([2,1]), [Transformation([1,2])]],
                   [Transformation([2,2]), [Transformation([2,2])]],
                   [Transformation([1,1]), [Transformation([1,1])]]]);

if not(IsRelationalMorphism(ex2theta, ex2phi, OnPoints, OnPoints)) then
  Display("Example 2 OK");
else
  Error("Example 2");
fi;

### EXAMPLE 3 #######################
# T2 to itself, isomorphism
ex3theta := HashMap(List([1,2], x-> [x,[x]]));
ex3phi := HashMap(List(FullTransformationSemigroup(2), s-> [s,[s]]));

if IsRelationalMorphism(ex3theta, ex3phi, OnPoints, OnPoints) then
  Display("Example 3 OK");
else
  Error("Example 3");
fi;

### FULL TRANSFORMATION SEMIGROUPS #######################
# T3 to T2 Zeiger encoding
# deciding whether a transformation is actually a permutation
IsPermutation := function(t)
  return DegreeOfTransformation(t)
         =
         Size(AsSet(ImageListOfTransformation(t)));
end;

# creates a relation on states for the full transformation semigroup, Zeiger encoding?
theta4n := function(n)
  return HashMap(List([1..n],
                      x -> [x, Difference([1..n],[x])]));
end;



# if it is a permutation, then leave, otherwise to a set of constant maps to points
# not in the image
phi4S := function(S)
  local f,n;
  n := DegreeOfTransformationSemigroup(S);
  f := function(s)
    if IsPermutation(s) then
      return [s];
    else
      # warning: giving n to ImageListOfTransformation is crucial here!
      # otherwise, we may add constant maps for the ignored highest fixed point(s)
      return List(Difference([1..n],AsSet(ImageListOfTransformation(s,n))),
                  x -> ConstantTransformation(n,x));
    fi;
  end;
  return HashMap(List(S, s -> [s, f(s)]));
end;

ex4theta := theta4n(3);
ex4phi := phi4S(FullTransformationSemigroup(3));

#is it a relational morphism
Print(IsRelationalMorphism(ex4theta, ex4phi, OnPoints, OnPoints));

#checking the morphism into the coordinatized form
Print(IsRelationalMorphism(Psi(ex4theta),
                           Mu(ex4theta, ex4phi,3),
                           OnPoints,
                           OnCoordinates));

# and back, from the cascade to the original
Print(IsRelationalMorphism(InvertHashMap(Psi(ex4theta)),
                           InvertHashMap(Mu(ex4theta, ex4phi,3)),
                           OnCoordinates,
                           OnPoints),"\n");


ex5theta := theta4n(5);
ex5phi := phi4S(FullTransformationSemigroup(5));
Print(IsRelationalMorphism(Psi(ex5theta),
                           Mu(ex5theta, ex5phi,5),
                           OnPoints,
                           OnCoordinates));

Print(IsRelationalMorphism(InvertHashMap(Psi(ex5theta)),
                           InvertHashMap(Mu(ex5theta, ex5phi,5)),
                           OnCoordinates,
                           OnPoints));


S := RandomSemigroup(IsTransformationSemigroup, 3,5);
Print(IsRelationalMorphism(Psi(theta4n(5)), Mu(theta4n(5),phi4S(S),5), OnPoints, OnCoordinates));
