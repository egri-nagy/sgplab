# general functions for (relational) morphisms
# using hash-maps for representing relations
# working on the covering Lemma algorithm

# to apply a binary operation for all ordered pairs for set A and B
# meant to be used in relational morphisms
ElementwiseProduct := function(A, B, binop)
  return AsSet(List(EnumeratorOfCartesianProduct(A,B),
                    p -> binop(p[1],p[2])));
end;

# how to define a relational morphism? from (X,S) to (Y,T)?
# theta, phi: hashmaps - they have the sources, assumed to be complete
# using loops so we can provide details when the morphism fails
IsRelationalMorphism := function(theta, phi, Sact, Tact)
  local x,s,
        inS, inT; #where is the action computed
  for x in Keys(theta) do
    for s in Keys(phi) do
      inS := theta[Sact(x,s)];
      inT := ElementwiseProduct(theta[x], phi[s], Tact);
      if not (IsSubset(inS, inT)) then
        Print("Checking ", x, "*", s, "\n"); #TODO: use Info once in SgpDec
        Print(inT, " is not a subset of ", inS, "\n");
        return false;
      fi;
    od;
  od;
  return true;
end;

# the graph of a relation, i.e. all related pairs
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
           Perform(rel[k], #we put all related elements into the mutable lists
                  function(v)
                    AddSet(m[v], k);
                  end);
         end);
  return m;
end;

# classifying a collection based on the output of a function
# the output of the function is the key and value is the collection of elts
# producing that value
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
