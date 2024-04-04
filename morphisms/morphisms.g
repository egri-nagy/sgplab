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

# it is injective if the inverse has singletons, i.e. the preimages are singletons
IsInjectiveHashMap := function(rel)
  return ForAll(Values(InvertHashMap(rel)), coll -> Size(coll) = 1);
end;

#doing it a bit more efficiently, to see if there is any overlap between the image
# sets we have seen so far
IsInjectiveHashMap2 := function(rel)
  local coll,imgs;
  coll := [];
  for imgs in Values(rel) do
    if not IsEmpty(Intersection(coll,imgs)) then
      return false; #not injective
    fi;
    coll := Union(coll, imgs); #collect all the elements so far
  od;
  return true; #there was no overlap, so it is injective
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

# just a quick check for hashmap equality
# it may miss list equality for values (if not sorted) 
HashMapEq := function(m1, m2)
  return (AsSet(Keys(m1)) = AsSet(Keys(m2)))
         and
         ForAll(Keys(m1), k -> m1[k]=m2[k]);
end;

## RELATIONAL MORPHISMS ##############################################

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

### trying to do the simplified algorithm
# returns a function that maps the elements down to the integers
# 1..., as many as needed.
# A - a set of states (positive integers)
W := function(A)
  local m, sA;
  sA := AsSortedList(A);
  m := HashMap();
  Perform(List([1..Size(sA)]), function(i) m[sA[i]]:=i;end);
  return x -> m[x];
end;

# the inverse of W
Winv := function(A)
  local m, sA;
  sA := AsSortedList(A);
  m := HashMap();
  Perform(List([1..Size(sA)]), function(i) m[i]:=sA[i];end);
  return x -> m[x];
end;

# the lifts in the decomposition for the states in the original ts 
Psi := function(theta)
  local psi, x, y, w, YtoX;
  psi := EmptyClone(theta);
  YtoX := InvertHashMap(theta);
  for x in Keys(theta) do
    for y in theta[x] do
      w:=W(YtoX[y]); 
      AddSet(psi[x], [y,w(x)]);
    od;
  od;
  return psi;
end;

#
LocalTransformation := function(y,s,t, YtoX)
local wyinv, wyt, l,n;
n := Maximum(Size(YtoX[y]), Size(YtoX[OnPoints(y,t)])); #we have to adjust for the bigger context
l := List([1..n], x->x);
  wyinv := Winv(YtoX[y]);
  wyt := W(YtoX[OnPoints(y,t)]);
Perform([1..Size(YtoX[y])],
                   function(k) l[k]:= wyt(OnPoints(wyinv(k),s));end);
return Transformation(l); 
end;

MuLift := function(s,t,theta,n)
  local y, cs, deps, nt, YtoX, preimgs;
    YtoX := InvertHashMap(theta);
      deps := [];
      for y in DistinctElts(Values(theta)) do
        nt := LocalTransformation(y,s,t, YtoX);
        #Print(nt, "\n");
        if not IsOne(nt) then
          Add(deps, [[y], nt]);
        fi;
      od;#y
  return Cascade([n, Maximum(List(DistinctElts(Values(theta)), y -> Size(YtoX[y])))],
  Concatenation([[[], t]], deps));
end;

Mu := function(theta, phi,n)
  local mu, t, y, s, cs, deps, nt;
  mu := EmptyClone(phi);
  for s in Keys(phi) do
    for t in phi[s] do
         cs := MuLift(s,t,theta,n);
      AddSet(mu[s],cs);
    od;#t
  od;#s
  return mu;
end;

# Detailed testing script for emulating by a cascade product
# creates a 2-level decomposition for the given semigroup and tests the
# emulation both ways
# uses the covering relmorphism
TestEmulation := function(S)
  local theta, phi, psi, mu, n, lifts;
  n := DegreeOfTransformationSemigroup(S);
  #the standard covering map described in the Covering Lemma paper
  theta := ThetaForDegree(n);
  phi := PhiForTransformationSemigroup(S);
  #1st to double check that we have a relational morphism
  Print("Surjective morphism works? ",
        IsRelationalMorphism(theta, phi, OnPoints, OnPoints),
        "\n");
  #now creating the coordinatized version
  psi := Psi(theta);
  mu := Mu(theta, phi, n);
  # Can the cascade emulation the original
  Print("Emulation works? ",
        IsRelationalMorphism(psi, mu, OnPoints, OnCoordinates),
        "\n");
  Print("Reverse works? ",
        IsRelationalMorphism(InvertHashMap(psi),
                             InvertHashMap(mu),
                             OnCoordinates,
                             OnPoints),
        "\n");
  lifts := DistinctElts(Values(mu));
  #the size calculation might be heavy for bigger cascade products
  Print("|S|=", Size(S), " -> (",
  Size(lifts) , ",",
  Size(Semigroup(lifts)), ",",
  Size(Semigroup(Concatenation(List(Generators(S), s-> mu[s])))),
  ") (#lifts, #Sgp(lifts), #Sgp(mu(Sgens)))");
end;

ThetaFromHolonomy := function(sk)
  local theta;
  theta := HashMap();
  Perform(List[1..DegreeOfSkeleton(sk)],
        function(x)
          local lifts;
          lifts :=  AsSet(List(AllHolonomyCoords(x,sk), First));
          #something to think about
          theta[x] := Interpret(sk,1, );
        end);
end;
