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
