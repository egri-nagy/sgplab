# general functions for (relational) morphisms
# aims to be more flexible by using hash-maps

# checking f:S->T homomorphism; Sop, Top are binary operations
# T is not needed as elements in T will be determined by f
IsHomomorphism := function(S, Sop, Top, f)
  return ForAll(EnumeratorOfCartesianProduct(S,S),
                s -> f(Sop(s[1], s[2])) #mult in S, go to T by f
                =
                Top(f(s[1]),f(s[2]))); #take elements to T, mult there
end;

# to apply a binary operation for all ordered pairs for set A and B
# meant to be used in relational morphisms
ElementwiseProduct := function(A, B, binop)
  return AsSet(List(EnumeratorOfCartesianProduct(A,B),
                    p -> binop(p[1],p[2])));
end;

# how to define a relational morphism? from (X,S) to (Y,T)?
# theta, phi: hashmaps - they have the sources, assumed to be complete
IsRelationalMorphism := function(theta, phi, Sact, Tact)
  return ForAll(EnumeratorOfCartesianProduct(Keys(theta), Keys(phi)),
                p -> IsSubset(theta[Sact(p[1],p[2])],
                             ElementwiseProduct(theta[p[1]], phi[p[2]], Tact)));
end;

