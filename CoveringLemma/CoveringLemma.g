# working on the covering Lemma algorithm

# using hash-maps for representing relations
Read("hashmap.g");

## RELATIONAL MORPHISMS ##############################################

# to apply a binary operation for all ordered pairs for set A and B
# meant to be used in relational morphisms, only distinct elements returned
ElementwiseProduct := function(A, B, binop)
  return AsSet(List(EnumeratorOfCartesianProduct(A,B),
                    p -> binop(p[1],p[2])));
end;

# how to define a relational morphism? from (X,S) to (Y,T)?
# theta: for states, hashmap from X to subsets of Y
# phi: for transformations, hashmap from S to subsets of T
# Sact, Tact: functions for the actions in the ts's, e.g., OnPoints
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

### CREATING A SURJECTIVE MORPHISM, constructing theta and phi - the default method

# STATES: subsets of the state set missing one point
# creates a relation on states for the full transformation semigroup
# a state goes to a set of all states except itself
ThetaForDegree := function(n) #we only need the number of states, the degree
  return HashMap(List([1..n],
                      x -> [x, Difference([1..n],[x])]));
end;

# TRANSFORMATIONS: permutations or constant maps

# deciding whether a transformation is actually a permutation
# note: IsPerm is about the type of the object
IsPermutation := function(t)
  return DegreeOfTransformation(t)
         =
         Size(AsSet(ImageListOfTransformation(t)));
end;

# if it is a permutation, then the image is the same,
# otherwise to a set of constant maps to points not in the image
PhiForTransformationSemigroup := function(S)
  local f,n;
  n := DegreeOfTransformationSemigroup(S);
  f := function(s)
    if IsPermutation(s) then
      return [s]; # still a set, but a singleton
    else
      # warning: giving n to ImageListOfTransformation is crucial here!
      # otherwise, we may add constant maps for the ignored highest fixed point(s)
      return List(Difference([1..n],AsSet(ImageListOfTransformation(s,n))),
                  x -> ConstantTransformation(n,x));
    fi;
  end;
  return HashMap(List(S, s -> [s, f(s)]));
end;

### BUILDING THE EMULATION constructing psi and mu ##############################

# LABELLING i.e. constructing (Z,U)

# STATES
# returns a function that maps the elements of a set of k integers down to the
# the set 1,...,n, 'squashing them to the bottom'
# A - a set of states (positive integers)
# it returns fail if the input is undefined (by the hashmap inside)
# intuition: this encodes the original states in X into Z
W := function(A)
  local m, sA;
  sA := AsSortedList(A); #to make sure they are in order
  m := HashMap();
  Perform(List([1..Size(sA)]), function(i) m[sA[i]]:=i;end);
  return x -> m[x];
end;

# the inverse of W, decodes the states in U back to ones from X
Winv := function(A)
  local m, sA;
  sA := AsSortedList(A);
  m := HashMap();
  Perform(List([1..Size(sA)]), function(i) m[i]:=sA[i];end);
  return x -> m[x];
end;

# the lifts in the decomposition for the states in the original ts
# idea: take a state x, and for all of its images y (the top level coordinate),
# find all the pre-images of y (the context)
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

# TRANSFORMATIONS
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
  for y in DistinctValueElements(theta) do
    nt := LocalTransformation(y,s,t, YtoX);
    #Print(nt, "\n");
    if not IsOne(nt) then
      Add(deps, [[y], nt]);
    fi;
  od;#y
  return Cascade([n, Maximum(List(DistinctValueElements(theta), y -> Size(YtoX[y])))],
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
  lifts := DistinctValueElements(mu);
  #the size calculation might be heavy for bigger cascade products
  Print("|S|=", Size(S), " -> (",
        Size(lifts) , ",",
        Size(Semigroup(lifts)), ",",
        Size(Semigroup(Concatenation(List(Generators(S), s-> mu[s])))),
        ") (#lifts, #Sgp(lifts), #Sgp(mu(Sgens)))");
end;

#WIP
ThetaFromHolonomy := function(sk)
local theta;
  theta := HashMap();
  Perform([1..(DegreeOfSkeleton(sk))],
         function(x)
           local lifts;
           lifts :=  AsSet(List(AllHolonomyCoords(x,sk), First));
           #something to think about
           theta[x] := Interpret(sk,1, x);
         end);
end;
