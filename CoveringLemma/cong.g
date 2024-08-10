# LATTICE ###############################################
StateSetCongruenceMeet := function(alpha, beta,n)
  return CompletePartition(Intersection([alpha,beta]),n);
end;

IsClosedStateSetCongruence := function(alpha, gens, n)
  return AsSet(CompletePartition(alpha,n)) = AsSet(StateSetCongruence(gens,alpha));
end;

FindNonMeet := function(N)
  local S,alpha, beta, m;
  repeat
    S := (RandomSemigroup(IsTransformationSemigroup, 2,N));
    alpha := StateSetCongruence(Generators(S), [ [1,2]]);
    beta := StateSetCongruence(Generators(S), [ [N-1,N]]);
    m := StateSetCongruenceMeet(alpha,beta,N);
    if Size(m) = N then Print("t\c"); fi;
    Print("#\c");
  until not (IsClosedStateSetCongruence(m, Generators(S),N));
  return S;
end;

StateSetCongruenceJoin := function(alpha, beta)
  return "still thinking";
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
        Print("#\c");
      fi;
    od;
  od;
  return congs;
end;

#### Experimental stuff ########################################################
# returns all pair-generated congruences of the given ts
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
