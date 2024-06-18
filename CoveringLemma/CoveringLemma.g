# Implementing the Covering Lemma as described in https://arxiv.org/abs/2404.11923


#WIP
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
  wy := wyLabel(thetainv[y]);
  wyinv := wyLabelInv(thetainv[y]);
  return AsSet(List(Staby(phi,y), s -> List([1..k],
                                  i -> wy(OnPoints(wyinv(i),s)))));
end;
