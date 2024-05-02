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
# Returns the coarsest congruence, in which the given seed sets are inside
# equivalence classes.
# seeds: disjoint sets of states
# gens: transformations, typically generators of the ts
StateSetCongruence := function(gens, seeds)
  local n, partition, m, collapsible;
  n := DegreeOfTransformationCollection(gens);
  partition := Concatenation(seeds, List(Difference([1..n], Union(seeds)), x->[x]));
  Perform(partition, Sort); #ugly but ok
  repeat
    m := ReverseLookup(partition);
    collapsible := ClassesToBeMerged(partition, m, gens);
    if not(IsEmpty(collapsible)) then
      partition := MergeClasses(partition, collapsible);
    fi;
  until IsEmpty(collapsible);
  #to guarantee that it is sorted
  return AsSortedList(List(partition, eqcl -> AsSortedList(eqcl)));
end;

#### now the Covering Lemma stuff #####################################################
ThetaFromCongruence := function(partition)
  local rl, pairs;
  rl := ReverseLookup(partition);
  pairs := List(partition, #go through all equivalence classes
                eqcl -> List(eqcl, #for all points we map them to their eqclass index
                             x -> [x, [Position(partition, rl[x])]]));
  return HashMap(Concatenation(pairs));
end;

# S - set of transformations, not necessarily a semigroup
PhiFromCongruence := function(partition, S)
  local rl, congact;
  rl := ReverseLookup(partition);
  congact := function(s)
    return Transformation(List(partition,
                               eqcl ->
                                    Position(partition,
                                             rl[First(OnSets(eqcl,s))])));
  end;
  return HashMap(List(S, s ->[s, [congact(s)]]));
end;

FishForInterestingExamples := function()
  local S, partition;
  while (true) do
    S := (RandomSemigroup(IsTransformationSemigroup,2,13));
    partition :=StateSetCongruence(Generators(S), [[1,2],[3,4]]);
    if (5 <= Size(Filtered(partition, A -> Size(A) > 1))) then
      Print("S := Semigroup(",Generators(S), ");\n", partition, "\n");
    fi;
  od;
end;
