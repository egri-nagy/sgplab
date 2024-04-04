# when working on the Covering Lemma paper's algorithm the kernel seemed to be very important
# but later it turned out to be unnecessary to compute it explicitly

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

