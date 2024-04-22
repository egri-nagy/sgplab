# example computation for the paper
S := Semigroup([Transformation([13,5,2,2,11,1,10,7,6,1,3,11,11]),
                Transformation([12,8,10,10,13,6,13,7,7,3,13,7,13])]);

#partition
pt := StateSetCongruence(Generators(S), [[1,2], [3,4]]);

IsRelationalMorphism(CongTheta(pt), CongPhi(pt, S), OnPoints, OnPoints);

IsRelationalMorphism(Psi(CongTheta(pt)), Mu(CongTheta(pt),CongPhi(pt, S)), OnPoints, OnCoordinates);

T := Semigroup(Concatenation(List(Generators(S), s -> CongPhi(pt, S)[s])));
# maybe this is not too good example, as the groups stay on top TODO: check that they are not repeated
