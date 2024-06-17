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
