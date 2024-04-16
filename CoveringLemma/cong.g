### creating congruences on X for (X,S)
# the algorithm is similar to the classical DFA minimization

#gives classes to be merged if needed, if everything checks, then return empty list
#going through all classes and generators
TryToCollapse := function(eqcls, lookup, gens)
  local g, eqcl, result;
  for g in gens do
    for eqcl in eqcls do
      result := AsSet(List(eqcl, x -> lookup[OnPoints(x,g)]));
      if Size(result) > 1 then return result; fi;
    od;
  od;
  return [];
end;

# given a partition and classes to be merged, it returns a new partiton
# with merged classes
# DANGER we silently assume the classes are ordered
MergeClasses := function(partition, tomerge)
  return Concatenation(Difference(partition, tomerge), [Union(tomerge)]);
end;

#gives a lookup for an element to the class it belongs to
ReverseLookup := function(partition)
  return HashMap(Concatenation(List(partition,
                                    eqcl -> List(eqcl,
                                                 x -> [x, eqcl]))));
end;

### THE MAIN FUNCTION TO CALL
StateCongruenceBySeed := function(S, seed)
  local n, partition, m, gens, collapsible;
  n := DegreeOfTransformationCollection(S);
  partition := Concatenation([seed], List(Difference([1..n], seed), x->[x]));
  Perform(partition, Sort); #ugly but ok
  gens := S;#Generators(S);
  repeat
    m := ReverseLookup(partition);
    collapsible := TryToCollapse(partition, m, gens);
    if not(IsEmpty(collapsible)) then
      partition := MergeClasses(partition, collapsible);
    fi;
  until IsEmpty(collapsible);
  return partition;
end;

#### now the Covering Lemma stuff #####################################################
CongTheta := function(partition)
  local sorted,rl;
  sorted := AsSortedList(List(partition, eqcl -> AsSortedList(eqcl)));
  rl := ReverseLookup(sorted);
  return HashMap(Concatenation(List(sorted,
                                    eqcl -> List(eqcl,
                                                 x -> [x, [Position(sorted, rl[x])]]))));
end;

CongPhi := function(partition, S)
  local sorted,rl;
  sorted := AsSortedList(List(partition, eqcl -> AsSortedList(eqcl)));
  rl := ReverseLookup(sorted);
  return HashMap(List(S,
                      s -> [s, [Transformation(List(sorted,
                                                    eqcl -> Position(sorted,
                                                                     rl[First(OnSets(eqcl,s))])))]]));
end;


