Read("morphisms.g");

S := Semigroup(Transformation([1,3,2]),
               Transformation([1,1,1]),
               Transformation([2,2,2]));

theta := HashMap([[1,[1]],
                  [2,[2]],
                  [3,[2]]]);

phi := HashMap([[Transformation([1,2,3]), [Transformation([1,2])]],
                [Transformation([1,1,1]), [Transformation([1,1])]],
                [Transformation([2,2,2]), [Transformation([2,2])]],
                [Transformation([3,3,3]), [Transformation([2,2])]],
                [Transformation([1,3,2]), [Transformation([1,2])]]]);
