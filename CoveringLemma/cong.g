### creating congruences on X for X,S

#gives classes to be merged if needed, if everything checks, then return empty list
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

MergeClasses := function(partition, tomerge)
  return Concatenation(Difference(partition, tomerge), [Union(tomerge)]);
end;

ReverseLookup := function(partition)
  return HashMap(Concatenation(List(partition,
                                    eqcl -> List(eqcl,
                                                 x -> [x, eqcl]))));
end;

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

StateCongruenceBySeed := function(S, seed)
  local n, partition, m, gens, collapsible;
  n := DegreeOfTransformationSemigroup(S);
  partition := Concatenation([seed], List(Difference([1..n], seed), x->[x]));
  Perform(partition, Sort); #ugly but ok
  gens := Generators(S);
  repeat
    m := ReverseLookup(partition);
    collapsible := TryToCollapse(partition, m, gens);
    if not(IsEmpty(collapsible)) then
      partition := MergeClasses(partition, collapsible);
    fi;
  until IsEmpty(collapsible);
  return partition;
end;

