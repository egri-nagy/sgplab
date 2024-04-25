Read("CoveringLemma.g");

### EXAMPLE 1 a minimal meaningful example of a surjective morphism
# joining two states with a transposition defined on them
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

TestEmulationWithMorphism(ex1S, ex1theta, ex1phi);
TestEmulation(ex1S);

#PrintTo("ex1mk.dot", DotMorphismKernel(MorphismKernelObjects(ex1theta), MorphismKernelArrows(ex1theta, ex1phi, OnPoints), OnPoints, OnPoints));


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
# T3 to itself, isomorphism
ex3theta := HashMap(List([1,2,3], x-> [x,[x]]));
ex3phi := HashMap(List(FullTransformationSemigroup(3), s-> [s,[s]]));

if IsRelationalMorphism(ex3theta, ex3phi, OnPoints, OnPoints) then
  Display("Example 3 OK");
else
  Error("Example 3");
fi;

### FULL TRANSFORMATION SEMIGROUPS #######################
# T3 to T2 Zeiger encoding

ex4theta := ThetaForDegree(3);
ex4phi := PhiForTransformationSemigroup(FullTransformationSemigroup(3));

#is it a relational morphism
Print(IsRelationalMorphism(ex4theta, ex4phi, OnPoints, OnPoints));

#checking the morphism into the coordinatized form
Print(IsRelationalMorphism(Psi(ex4theta),
                           Mu(ex4theta, ex4phi),
                           OnPoints,
                           OnCoordinates));

# and back, from the cascade to the original
Print(IsRelationalMorphism(InvertHashMapRelation(Psi(ex4theta)),
                           InvertHashMapRelation(Mu(ex4theta, ex4phi)),
                           OnCoordinates,
                           OnPoints),"\n");


ex5theta := ThetaForDegree(5);
ex5phi := PhiForTransformationSemigroup(FullTransformationSemigroup(5));
Print(IsRelationalMorphism(Psi(ex5theta),
                           Mu(ex5theta, ex5phi),
                           OnPoints,
                           OnCoordinates));

Print(IsRelationalMorphism(InvertHashMapRelation(Psi(ex5theta)),
                           InvertHashMapRelation(Mu(ex5theta, ex5phi)),
                           OnCoordinates,
                           OnPoints));


S := RandomSemigroup(IsTransformationSemigroup, 3,5);
Print(IsRelationalMorphism(Psi(ThetaForDegree(5)), Mu(ThetaForDegree(5),PhiForTransformationSemigroup(S)), OnPoints, OnCoordinates));

##
IdTheta := function(states)
  return HashMap(List(states, x-> [x,[x]]));
end;

# this is not a morphism
NoPermPhi := function(S)
  return HashMap(List(S, function(s)
                       if IsPermutation(s) then
                         return [s,[IdentityTransformation]];
                       else
                         return [s,[s]];
                       fi;end));
end;

### trying to fix the bad example
ex6S := Semigroup(Transformation([2,3,1,5,4]));

ex6theta := HashMap([[1,[1]],
                     [2,[1]],
                     [3,[1]],
                     [4,[2]],
                     [5,[2]]]);

