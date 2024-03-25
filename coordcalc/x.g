collapser := Cascade([4,6], [[[], Transformation([1,1,1,1])],
			    [[1], Transformation([2,2,3])],
			    [[2], Transformation([1,3,3])],
			    [[3], Transformation([1,2,2])]]);
transposition := Cascade([4,6], [[[], Transformation([2,1,3,4])]]);
cycle := Cascade([4,6], [[[], Transformation([2,3,4,1])]]);

S4wrT3 := Semigroup(collapser, transposition, cycle);
