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

## KERNEL FUNCTIONS ##################################################
#new attempt - to find the arrows for a single tranformation
TransformationInTheKernel := function(s, theta, phi, Sact, Tact)
  local ys, xs, ts, x, y, t;
  xs := Keys(theta);
  ts := phi[s]; #all the lifts for s
  Print("Analyzing s:",s,"\n");
  for t in ts do
    Print("Lifted to t:",t,"\n");
    for x in xs do
      ys := theta[x]; #all the lifts of x
      for y in ys do
        Print("(", x, ",", y, ")->(", Sact(x,s),",",Tact(y,t),")\n");
      od;
    od;
  od;
  Print("\n");
end;


# identifying arrows with the same action
Identify := function(arrows, YtoX, Sact)
  local m;
  m := Classify(arrows,
                arrow -> List(AsSet(YtoX[arrow[1]]),
                              x-> Sact(x, arrow[2])));
  return List(Keys(m), k -> First(m[k])); #just get the first in the group
end;

MorphismKernelObjects := function(theta) #TODO this is just a synonym
  return HashMapGraph(theta);
end;

# computes the kernel of the relational morphism
MorphismKernelArrows := function(theta, phi, Sact)
local ys, yts, ts, YtoX, TtoS, triples, identified;
  ys := DistinctElts(Values(theta));
  YtoX := InvertHashMap(theta);
  ts := DistinctElts(Values(phi));
  TtoS := InvertHashMap(phi);
  yts := Cartesian(ys,ts);
  # these triples will be the arrow labels, for all (y,t) pairs we put
  # an s in between it is a preimage of y
  triples := List(yts, p -> List(TtoS[p[2]],
                                 s -> [p[1], s, p[2] ])); #no identification yet
  Print(Size(Concatenation(triples)), " triples ");
  identified := Concatenation(List(triples,
                                   arrows -> Identify(arrows, YtoX, Sact)));
  return identified;
 end;

str := function(object) local s; s := String(object); RemoveCharacters(s," "); return s;end;

DotMorphismKernel := function(objects, arrows, Sact, Tact)
  local gens, dot, i, o2n, y,s,t, y2xypairs, src, trg, edge, edges2labels, a, label, labels;

  dot:="";
  Append(dot, "//dot\ndigraph morphismkernel{\n");
  #Append(str, "node [shape=circle]");
  #Append(str, "edge [len=1.2]");
  o2n := HashMap(); # object to node names
  for i in [1..Size(objects)] do
    o2n[objects[i]] := JoinStringsWithSeparator(["n", str(i)],"");
    Append(dot, JoinStringsWithSeparator(["n", str(i), "[label=\"", str(objects[i]), "\"]\n"],""));
  od;
  #classifying the objects (x,y) pairs by the second element,
  #thus getting a lookup for the pairs based on y
  y2xypairs := Classify(objects, l->l[2]);
  edges2labels := HashMap();
  for a in arrows do
    y := a[1];
    s := a[2];
    t := a[3];
    for src in y2xypairs[y] do
      trg := [Sact(src[1], s), Tact(src[2], t)];
      edge := Concatenation(o2n[src],"->",o2n[trg]);
      if src <> trg then
        label := Concatenation(str(ImageListOfTransformation(s)), ",", str(ImageListOfTransformation(t)));
        if IsBound(edges2labels[edge]) then
          Add(edges2labels[edge], label);
        else
          edges2labels[edge] := [label];
        fi;
      fi;
    od;
  od;
  for edge in Keys(edges2labels) do
    labels := edges2labels[edge];
    Append(dot, JoinStringsWithSeparator([edge, "[label=\"",
                                          str(labels[1]), #the first one goes into label
                                          "\", tooltip=\"",
                                          JoinStringsWithSeparator(labels{[2..Size(labels)]},"|"),
                                          "\"]\n"],""));
  od;
  Append(dot,"}\n");
  return dot;
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
#if (Size(l) = 1) then return IdentityTransformation;
#else 
return Transformation(l); 
#fi;
end; #we take a point k

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

HashMapEq := function(m1, m2)
  return (AsSet(Keys(m1)) = AsSet(Keys(m2)))
         and
         ForAll(Keys(m1), k -> m1[k]=m2[k]);
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
