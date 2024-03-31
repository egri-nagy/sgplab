# general functions for (relational) morphisms
# using hash-maps for representing relations
# working on the covering Lemma algorithm

## HashMap functions ##################
# used for getting distinct values from relations (set-valued hashmap values)
# for now we represent morphisms completely, not by generators

DistinctElts := function(coll)
  return AsSet(Concatenation(AsSet(coll)));
end;

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

# the graph of a relation, i.e. all related pairs
HashMapGraph := function(rel)
  return Concatenation(List(Keys(rel),
                            k -> List(rel[k],
                                      v -> [k,v])));
end;

# creates a new set-valued hashmap using the same keys but with empty value sets
EmptyClone := function(hashmap)
  return HashMap(List(Keys(hashmap),
                      key -> [key, []]));

end;
## RELATIONAL MORPHISMS ##############################################
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

### CREATING A SURJECTIVE MORPHISM, constructing theta and phi
# states: subsets of the state set missing one point
# transformations: permutations or constant maps

# deciding whether a transformation is actually a permutation
# note: IsPerm is about the ype of the object
IsPermutation := function(t)
  return DegreeOfTransformation(t)
         =
         Size(AsSet(ImageListOfTransformation(t)));
end;

# creates a relation on states for the full transformation semigroup
# a state goes to a set of all states except itself
ThetaForDegree := function(n) #we only need the number of states, the degree
  return HashMap(List([1..n],
                      x -> [x, Difference([1..n],[x])]));
end;

# if it is a permutation, then leave, otherwise to a set of constant maps to points
# not in the image
PhiForTransformationSemigroup := function(S)
  local f,n;
  n := DegreeOfTransformationSemigroup(S);
  f := function(s)
    if IsPermutation(s) then
      return [s];
    else
      # warning: giving n to ImageListOfTransformation is crucial here!
      # otherwise, we may add constant maps for the ignored highest fixed point(s)
      return List(Difference([1..n],
                             AsSet(ImageListOfTransformation(s,n))),
                  x -> ConstantTransformation(n,x));
    fi;
  end;
  return HashMap(List(S, s -> [s, f(s)]));
end;

### BUILDING THE EMULATION constructing psi and mu ##############################

# LABELLING
# gives a function that maps n points to n-1 by skipping i,
# n degree, i is the hole
w := function(i)
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
winv := function(i)
  return function(k)
    if k < i then
      return k;
    else
      return k+1;
    fi;
  end;
end;

# making a transformation from an arrow in the kernel
Arrow2Transformation := function(y,s,t,n)
  return Transformation
             (List([1..n], #should this be n-1?, nope it doesn't work that way
                   k -> w(OnPoints(y,t))(OnPoints(winv(y)(k),s))));
end; #we take a point k

## Covering Lemma
Psi := function(theta)
  local psi, x, y;
  psi := EmptyClone(theta);
  for x in Keys(theta) do
    for y in theta[x] do
      AddSet(psi[x], [y,w(y)(x)]);
    od;
  od;
  return psi;
end;

Mu := function(theta, phi,n)
  local mu, t, y, s, cs, deps, nt;
  mu := EmptyClone(phi);
  for s in Keys(phi) do
    for t in phi[s] do
      deps := [];
      for y in DistinctElts(Values(theta)) do
        nt := Arrow2Transformation(y,s,t,n-1);
        if not IsOne(nt) then
          Add(deps, [[y], nt]);
        fi;
      od;#y
      cs := Cascade([n, n-1],Concatenation([[[], t]], deps));
      AddSet(mu[s],cs);
    od;#t
  od;#s
  return mu;
end;

TestEmulation := function(S)
  local theta, phi, psi, mu, n;
  n := DegreeOfTransformationSemigroup(S);
  theta := ThetaForDegree(n);
  phi := PhiForTransformationSemigroup(S);
  Print("Surjective morphism works? ",
        IsRelationalMorphism(theta, phi, OnPoints, OnPoints),
        "\n");
  psi := Psi(theta);
  mu := Mu(theta, phi, n);
  Print("Emulation works? ",
        IsRelationalMorphism(psi, mu, OnPoints, OnCoordinates),
        "\n");
  Print("Reverse works? ",
        IsRelationalMorphism(InvertHashMap(psi),
                             InvertHashMap(mu),
                             OnCoordinates,
                             OnPoints),
        "\n");
end;
