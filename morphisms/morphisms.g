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

RelationGraph := function(rel)
  return Concatenation(List(Keys(rel),
                            k -> List(rel[k],
                                      v -> [k,v])));
end;

# used for getting distinct values from relations (set-valued hashmap values)
DistinctElts := function(colls)
  return AsSet(Concatenation(AsSet(colls)));
end;

# turning around a hashmap
InvertRelation := function(rel)
  local m;
  #putting in all values as keys with empty value set for now
  m := HashMap(List(DistinctElts(Values(rel)),
                    x -> [x,[]]));
  Perform(Keys(rel),
         function(k)
           Perform(rel[k],
                  function(v)
                    AddSet(m[v], k);
                  end);
         end);
  return m;
end;

Classify := function(elts, f)
  local e, #an elemenet from elts
        d, #data constructed from e, f(e)
        m; #hashmap for the final result
  m := HashMap();
  for e in elts do
    d := f(e);
    if d in m then
      Add(m[d], e);
    else
      m[d] := [e];
    fi;
  od;
  return m;
end;


# computes the kernel of the relational morphism
MorphismKernel := function(theta, phi)
local ys, yts, ts, YtoX, TtoS;
  ys := DistinctElts(Values(theta));
  YtoX := InvertRelation(theta);
  ts := DistinctElts(Values(phi));
  TtoS := InvertRelation(phi);
  yts := Cartesian(ys,ts);
  # now classify these yt pairs based on what the corresponding s' do
  return List(yts, p -> List(TtoS[p[2]],
                             x -> [p[1], x, p[2] ])); #no identification yet
 end;
