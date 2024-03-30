Read("morphisms.g");

# a surjective morphism joining two states with a transposition
ex1S := Semigroup(Transformation([1,3,2]),
               Transformation([1,1,1]),
               Transformation([2,2,2]));

ex1theta := HashMap([[1,[1]],
                     [2,[2]],
                     [3,[2]]]);

ex1phi := HashMap([[Transformation([1,2,3]), [Transformation([1,2])]],
                   [Transformation([1,1,1]), [Transformation([1,1])]],
                   [Transformation([2,2,2]), [Transformation([2,2])]],
                   [Transformation([3,3,3]), [Transformation([2,2])]],
                   [Transformation([1,3,2]), [Transformation([1,2])]]]);

# not a relational morphism
ex2theta := HashMap([[1,[1]],
                     [2,[2]]]);

ex2phi := HashMap([[Transformation([1,2]), [Transformation([1,2])]],
                   [Transformation([2,1]), [Transformation([1,2])]],
                   [Transformation([2,2]), [Transformation([2,2])]],
                   [Transformation([1,1]), [Transformation([1,1])]]]);

# T2 to itself, isomorphism
ex3theta := HashMap(List([1,2], x-> [x,[x]]));
ex3phi := HashMap(List(FullTransformationSemigroup(2), s-> [s,[s]]));

# T3 to T2 Zeiger encoding
# deciding whether a transformation is actually a permutation
IsPermutation := function(t)
  return DegreeOfTransformation(t)
         =
         Size(AsSet(ImageListOfTransformation(t)));
end;

Tntheta := function(n)
  local f;
  f := function(x)
    local l;
    l := [1..n];
    Remove(l,x);
    return l;
  end;
  return HashMap(List([1..n], x -> [x, f(x)]));
end;

ex4theta := Tntheta(3);

Tnphi := function(n)
  local f;
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
  return HashMap(List(FullTransformationSemigroup(n),
                     s -> [s, f(s)]));
end;

ex4phi := Tnphi(3);

Print(IsRelationalMorphism(ex4theta, ex4phi, OnPoints, OnPoints));


