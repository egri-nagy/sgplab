### creating congruences on X for (X,S) for a surjective homomorphism
# the algorithm is similar to the classical DFA minimization
# TODO: GAP library has Partition although it is undocumented - check whether it is usable here or not


# Gives classes to be merged if needed, if everything checks, then it returns
# the empty list. Going through all classes and generators gens, but immediately
# returning the first found classes to be merged.
# eqcls - the equivalence classes so far
# lookup takes a point to its current equivalence class
ClassesToBeMerged := function(eqcls, gens)
  local g, eqcl, result, lookup;
  lookup := ReverseLookup(eqcls);
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
# Both Difference and Union return new lists, thus the partition is new.
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

# completes a set of disjoint sets into a partition of [1..n]
# by adding singleton sets for the missing states
CompletePartition := function(disjoint_sets, n)
  return Set(Concatenation(disjoint_sets,
                           List(Difference([1..n], Union(disjoint_sets)),
                                x->[x])));
end;

### THE MAIN FUNCTION TO CALL
# Returns the coarsest congruence, in which the given seed sets are inside
# equivalence classes.
# seeds: disjoint sets of states
# gens: transformations, typically generators of the ts
StateSetCongruence := function(gens, seeds)
  local n, partition, collapsible;
  n := DegreeOfTransformationCollection(gens);
  partition := CompletePartition(seeds,n);
  repeat
    collapsible := ClassesToBeMerged(partition, m, gens);
    if not(IsEmpty(collapsible)) then
      partition := MergeClasses(partition, collapsible);
    fi;
  until IsEmpty(collapsible);
  #to guarantee that it is sorted
  return AsSortedList(List(partition, eqcl -> AsSortedList(eqcl)));
end;

AllStateSetCongruences := function(gens)
  local n, alpha, beta, congs, waiting, seeds, ncong;
  n := DegreeOfTransformationCollection(gens);
  alpha := CompletePartition([],n);
  congs := HashSet();
  AddSet(congs, alpha);
  waiting := Stack();
  Push(waiting, alpha);
  while Size(waiting) > 0 do
    beta := Pop(waiting);
    for  seeds in IteratorOfCombinations(beta,2) do
      ncong := StateSetCongruence(gens,MergeClasses(beta, seeds));
      if not (ncong in congs) then
        AddSet(congs, ncong);
        Push(waiting, ncong);
      fi;
    od;
  od;
  return congs;
end;

#### now the Covering Lemma stuff #####################################################
ThetaForCongruence := function(partition)
  local rl, pairs;
  rl := ReverseLookup(partition);
  pairs := List(partition, #go through all equivalence classes
                eqcl -> List(eqcl, #for all points we map them to their eqclass index
                             x -> [x, [Position(partition, rl[x])]]));
  return HashMap(Concatenation(pairs));
end;

# S - set of transformations, not necessarily a semigroup
PhiForCongruence := function(partition, S)
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

#### Experimental stuff ########################################################
# returns all pair-generated congruences of the given ts
StateSetCongruenceMeet := function(alpha, beta,n)
  return CompletePartition(Intersection([alpha,beta]),n);
end;

PairGenerated := function(S) #
  return Set(List(Combinations([1..DegreeOfTransformationCollection(S)],2),
           pair -> StateSetCongruence(Generators(S), [pair])));
end;

# returns true if alpha is a finer partition than beta
IsFinerPartition := function(alpha, beta)
  return ForAll(alpha, A -> ForAny(beta, B -> IsSubset(B,A)));
end;

IsStrictlyFinerPartition := function(alpha, beta)
  return (alpha <> beta) and IsFinerPartition(alpha, beta);
end;

Atoms := function(S)
  local congs;
  congs := PairGenerated(S);
  return Filtered(congs,
                  alpha -> not (ForAny(congs,
                                       beta -> IsStrictlyFinerPartition(beta, alpha))));
end;

FishForInterestingExamples := function()
  local S, partition;
  while (true) do
    S := (RandomSemigroup(IsTransformationSemigroup,2,13));
    partition :=StateSetCongruence(Generators(S), [[1,2],[3,4]]);
    if (5 > Size(partition))
       and (2 < Size(partition))
       and (3 <= Size(Filtered(partition, A -> Size(A) > 2))) then
    Print("S := Semigroup(",Generators(S), ");\n", Size(S), " ",partition, "\n");
      DisplayHolonomyComponents(Skeleton(S));
    fi;
  od;
end;
