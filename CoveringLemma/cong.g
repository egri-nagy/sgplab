### creating congruences on X for (X,S) for a surjective homomorphism
# the algorithm is similar to the classical DFA minimization

# Gives classes to be merged if needed, if everything checks, then it returns
# the empty list. Going through all classes and generators gens, but immediately
# returning the first found classes to be merged.
# eqcls - the equivalence classes so far
# lookup takes a point to its current equivalence class
ClassesToBeMerged := function(eqcls, lookup, gens)
  local g, eqcl, result;
  for g in gens do
    for eqcl in eqcls do
      result := AsSet(List(eqcl, x -> lookup[OnPoints(x,g)]));
      if Size(result) > 1 then #some points in eqcl went to different classes
        return result;
      fi;
    od;
  od;
  return []; #all checks, nothing to merge
end;

# given a partition and classes to be merged, it returns a new partiton
# with merged classes
# removes the ones to be merged and adds their union
# DANGER we assume the classes are ordered, but Union silently applies Set
MergeClasses := function(partition, tomerge)
  return Concatenation(Difference(partition, tomerge),
                       [Union(tomerge)]);
end;

#gives a lookup for a point to the class it belongs to
ReverseLookup := function(partition)
  return HashMap(Concatenation(List(partition,
                                    eqcl -> List(eqcl,
                                                 x -> [x, eqcl]))));
end;

### THE MAIN FUNCTION TO CALL
StateCongruenceBySeed := function(gens, seeds)
  local n, partition, m, collapsible;
  n := DegreeOfTransformationCollection(S);
  partition := Concatenation(seeds, List(Difference([1..n], Union(seeds)), x->[x]));
  Perform(partition, Sort); #ugly but ok
  repeat
    m := ReverseLookup(partition);
    collapsible := ClassesToBeMerged(partition, m, gens);
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


