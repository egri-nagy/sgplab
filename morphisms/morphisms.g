# general functions for (relational) morphisms
# using hash-maps for representing relations
# working on the covering Lemma algorithm

## HashMap functions ##################
# turning around a hashmap
InvertHashMap := function(rel)
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


# computes the kernel of the relational morphism
MorphismKernel := function(theta, phi, Sact)
local ys, yts, ts, YtoX, TtoS, triples, identify;
  ys := DistinctElts(Values(theta));
  YtoX := InvertHashMap(theta);
  ts := DistinctElts(Values(phi));
  TtoS := InvertHashMap(phi);
  yts := Cartesian(ys,ts);
  triples := List(yts, p -> List(TtoS[p[2]],
                                 x -> [p[1], x, p[2] ])); #no identification yet
  identify := function(arrows) #TODO check this
    local m;
    m := Classify(arrows,
                  arrow -> List(AsSet(YtoX[arrow[1]]),
                                      x-> Sact(x, arrow[2])));
    return List(Keys(m), k -> First(m[k])); #just get the first in the group
  end;
  return Concatenation(List(triples, identify));
 end;

## labelling ##############################
# n degree, i is the hole
wi := function(i)
  return function(k)
    if k < i then
      return k;
    elif k > i then
      return k-1;
    else
      Error("There is no hole!");
    fi;
  end;
end;

# n degree, i is the hole, the inverse
wiinv := function(i)
  return function(k)
    if k < i then
      return k;
    else
      return k+1;
    fi;
  end;
end;

ArrowLabel := function(arrow,n)
  local i,s,t;
  i := arrow[1];
  s := arrow[2];
  t := arrow[3];
  return List([1..n], k -> wi(OnPoints(i,t))( OnPoints(wiinv(i)(k),s) ));
end;

## Covering Lemma
Psi := function(theta)
  local m, x, y;
  m := HashMap(List(Keys(theta), k -> [k,[]]));
  for x in Keys(theta) do
    for y in theta[x] do
      AddSet(m[x], [y,wi(y)(x)]);
    od;
  od;
  return m;
end;

Mu := function(theta, phi)
  return;
end;
