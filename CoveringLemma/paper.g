# example computation for the paper
S := Semigroup([Transformation([13,5,2,2,11,1,10,7,6,1,3,11,11]),
                Transformation([12,8,10,10,13,6,13,7,7,3,13,7,13])]);

#partition
partition := StateSetCongruence(Generators(S), [[1,2], [3,4]]);

theta := ThetaForCongruence(partition);
phi := PhiForCongruence(partition, S);

IsTSRelMorph(theta, phi, OnPoints, OnPoints);

IsTSRelMorph(Psi(theta), Mu(theta, phi), OnPoints, OnCoordinates);

T := Semigroup(Concatenation(List(Generators(S), s -> phi[s])));
# maybe this is not too good example, as the groups stay on top TODO: check that they are not repeated
