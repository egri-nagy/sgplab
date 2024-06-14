# Implementing the Covering Lemma as described in https://arxiv.org/abs/2404.11923

Read("hashmap.g");

### RELATIONAL MORPHISMS #######################################################


### CREATING SURJECTIVE MORPHISMS, constructing theta and phi #################

# STATES: subsets of the state set missing one point
# creates a relation on states for the full transformation semigroup
# a state goes to a set of all states except itself, self-inverse theta
# the n(n-1) - slowest decomposition method
ThetaForPermutationResets := function(n) #we only need the number of states, the degree
  return HashMap(List([1..n],
                      x -> [x, Difference([1..n],[x])]));
end;

# TRANSFORMATIONS: permutations or constant maps
# deciding whether a transformation is actually a permutation
# note: IsPerm is about the type of the object, not what it is doing
IsPermutation := function(t)
  return DegreeOfTransformation(t) #this seems to be computed by max moved point
         =
         Size(AsSet(ImageListOfTransformation(t)));
end;

# mapping s to phi(s) - a transformation to a set of transformations
# if it is a permutation, then the image is the same,
# otherwise to a set of constant maps to points not in the image
# the degree of transformation given by n
PermutationOrResets := function(s,n)
  if IsPermutation(s) then
    return [s]; # still a set, but a singleton
  else
    # warning: giving n to ImageListOfTransformation is crucial here!
    # otherwise, we may add constant maps for the ignored highest fixed point(s)
    return List(Difference([1..n],AsSet(ImageListOfTransformation(s,n))),
                x -> ConstantTransformation(n,x));
  fi;
end;

# complementing ThetaForPermutationResets
PhiForPermutationResets := function(S)
  local n;
  n := DegreeOfTransformationSemigroup(S);
  return HashMap(List(S, s -> [s, PermutationOrResets(s,n)]));
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
PsiFunc := function(x, theta, thetainv)
  return List(theta[x],
             function(y)
               local w;
               w := W(thetainv[y]);
               return [y,w(x)];
             end);
end;

Psi := function(theta)
  local x,YtoX, psi;
  psi := HashMap();
  YtoX := InvertHashMapRelation(theta);
  for x in Keys(theta) do
      psi[x] := PsiFunc(x, theta, YtoX);
  od;
  return psi;
end;

# for the coordinates we return the original state
# Where does z go? It depends on the top level state.
PsiInvFunc := function(coords,thetainv)
  local y,z,winv;
  y := coords[1];
  z:= coords[2];
  winv := Winv(thetainv[y]); # thetainv: Y -> X
  return winv(z);
end;

# checking to coordinatized states by mapping them back to X
PsiCheck := function(theta)
  local x, thetainv;
  thetainv := InvertHashMapRelation(theta);
  for x in Keys(theta) do
    if not (ForAll(PsiFunc(x, theta, thetainv),
                   coordpair -> x = PsiInvFunc(coordpair, thetainv))) then
      Print("Problem with state ",x );
    fi;
  od;
  return true;
end;

# TRANSFORMATIONS
# given the context y, the top level state, we want to know
# how the original action of s can be expressed locally on Z
# the element of U constructed here also depends on t
LocalTransformation := function(y,s,t, YtoX)
  local wyinv, wyt, l, ypre, ytpre;
  ypre := YtoX[y]; #preimages
  ytpre := YtoX[OnPoints(y,t)];
  l := [1..Maximum(Size(ypre),Size(ytpre))];#k]; #we need to prefill the action with identities, |ypre| may not equal |ytpre|
  wyinv := Winv(ypre);
  wyt := W(ytpre);
  Perform([1..Size(ypre)],
         function(z)
           # map z back from the current context,
           # act by S in X, then map to new context of yt
           l[z]:= wyt(OnPoints(wyinv(z),s));
         end);
  return Transformation(l);
end;

# creating a cascade for s when lifted to t
MuLift := function(s,t,theta,n)
  local y, cs, deps, nt, YtoX, preimgs,k;
  YtoX := InvertHashMapRelation(theta);
  deps := [];
  k :=  Maximum(List(ImageOfHashMapRelation(theta), y -> Size(YtoX[y])));
  for y in ImageOfHashMapRelation(theta) do
    nt := LocalTransformation(y,s,t, YtoX);
    if not IsOne(nt) then
      Add(deps, [[y], nt]);
    fi;
  od;#y
  if not IsOne(t) then Add(deps, [[],t]); fi; #top level is t
  return Cascade([n,k], deps, TransCascadeType);
end;

# needed for MuCheck
MuFunc := function(s, ts, theta, n)
  return List(ts, t-> MuLift(s,t,theta, n));
end;

# the complete map from S to the cascade product
# just lift every s with respect to all of its lifts
Mu := function(theta, phi)
  local mu, t, y, s, cs, deps, nt, n;
  n := Size(ImageOfHashMapRelation(theta)); # #states of top level
  mu := HashMap();
  for s in Keys(phi) do
    mu[s] := MuFunc(s, phi[s], theta,n);
  od;#s
  return mu;
end;

#returns a transformation in S
MuInvFunc := function(cs, theta)
  local y, wy,t,u,wytinv, thetainv,x, m,xs,n;
  thetainv := InvertHashMapRelation(theta);
  m := HashMap();
  n := Size(Keys(theta)); # |X|
  for y in ImageOfHashMapRelation(theta) do
    wy := W(thetainv[y]);
    t := OnDepArg([], DependencyFunctionsOf(cs)[1]);
    wytinv := Winv(thetainv[OnPoints(y,t)]);
    u := OnDepArg([y], DependencyFunctionsOf(cs)[2]);
    #Print(wy*u*wytinv);
    for x in thetainv[y] do
      xs :=  wytinv(OnPoints(wy(x),u));
      #Print(x , " -> ",xs, "\n");
      if IsBound(m[x]) then
        if m[x] <> xs then Error(); fi; #this can be removed later
      else
        m[x] := xs;
      fi;
    od;
  od;
  return Transformation(List([1..n], i -> m[i]));
end;

# checks whether the emulation composed with interpretation IE
# is the identity on S
MuCheck := function(theta, phi)
  local s, lifts,n,css, cs,ss;
  n := Size(ImageOfHashMapRelation(theta)); # |Y|
  for s in Keys(phi) do
    css := MuFunc(s, phi[s], theta, n);
    for cs in css do
      ss := MuInvFunc(cs,theta);
      if s <> ss then Print("s", s, " <> ss", ss, "\n"); return false; fi;
    od;
  od;
  return true;
end;

# Detailed testing script for emulating by a cascade product
# creates a 2-level decomposition for the given semigroup and input
# surjective morphism and tests the emulation and interpretations
TestEmulationWithMorphism := function(S,theta, phi)
  local psi, mu, lifts;
  #1st to double check that we have a relational morphism
  Print("Surjective morphism works? ",
        IsTSRelMorph(theta, phi, OnPoints, OnPoints),
        "\n");
  #now creating the coordinatized version
  psi := Psi(theta);
  mu := Mu(theta, phi);
  # Can the cascade emulation the original
  Print("Emulation works? ",
        IsTSRelMorph(psi, mu, OnPoints, OnCoordinates),
        "\n");
  Print("Interpretation works? ",
        IsTSRelMorph(InvertHashMapRelation(psi),
                             InvertHashMapRelation(mu),
                             OnCoordinates,
                             OnPoints),
        "\n");
  lifts := ImageOfHashMapRelation(mu);
  #the size calculation might be heavy for bigger cascade products
  Print("|S|=", Size(S), " -> (",
        Size(lifts) , ",",
        Size(Semigroup(lifts)), ",",
        Size(Semigroup(Concatenation(List(Generators(S), s-> mu[s])))),
        ") (#lifts, #Sgp(lifts), #Sgp(mu(Sgens)))");
end;

# creates the default n(n-1) covering
TestEmulation := function(S)
local n, theta, phi;
  n := DegreeOfTransformationSemigroup(S);
  #the standard covering map described in the Covering Lemma paper
  theta := ThetaForPermutationResets(n);
  phi := PhiForPermutationResets(S);
  TestEmulationWithMorphism(S, theta, phi);
end;

#WIP
ThetaForHolonomy := function(sk)
local theta;
  theta := HashMap();
  Perform([1..DegreeOfSkeleton(sk)],
         function(x)
           theta[x] := AsSet(List(AllHolonomyCoords(x,sk), First));
         end);
  return theta;
end;

PhiForHolonomy := function(sk)
local phi;
  phi := HashMap();
  Perform(TransSgp(sk),
         function(s)
           local top;
           top := AsHolonomyCascade(s,sk)[1];
           if IsEmpty(top) then
             phi[s] := [IdentityTransformation];
           else
             phi[s] := [top[1][2]];
           fi;
         end);
  return phi;
end;

####### extreme collapsing
#evertyhing goes to state 1
ThetaForConstant := function(states)
  return HashMap(List(states, x-> [x,[1]]));
end;

#everyting goes to the identity
PhiForConstant := function(transformations)
  return HashMap(List(transformations, s-> [s,[IdentityTransformation]]));
end;


##### local transformation monoid by idempotent e #############################
ThetaForLocalMonoid := function(states, e)
  return HashMap(List(states, x-> [x,[OnPoints(x,e)]]));
end;

PhiForLocalMonoid := function(transformations, e)
  return HashMap(List(transformations, s-> [s,[e*s*e]]));
end;

#it is a rare property - mostly just the identity or constant maps
TestForMorphicLocalMonoid := function(S)
return Filtered(Idempotents(S),
                e -> IsTSRelMorph(ThetaForLocalMonoid([1..DegreeOfTransformationSemigroup(S)],e),
                                          PhiForLocalMonoid(S, e),
                                          OnPoints, OnPoints));
end;

### computing the Uys
#all the s in S such that its image t fixes y
#for now this is a very expensive operation
Staby := function(phi,y)
local phiinv, ts;
  phiinv := InvertHashMapRelation(phi);
  ts := Filtered(Keys(phiinv),
                 t -> y = OnPoints(y,t));
  return AsSet(Concatenation(List(ts, t-> phiinv[t])));
end;

#for now, only for fully calculated ones
Uy := function(theta, phi, y)
  local wy, wyinv, thetainv,k;
  thetainv := InvertHashMapRelation(theta);
  k := Size(thetainv[y]);
  wy := W(thetainv[y]);
  wyinv := Winv(thetainv[y]);
  return AsSet(List(Staby(phi,y), s -> List([1..k],
                                  i -> wy(OnPoints(wyinv(i),s)))));
end;
