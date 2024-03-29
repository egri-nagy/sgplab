# brute-forcing morphic relations - this is the older attempt, mostly multiplication table based - OBSOLETE

# cross-multiplication of sets A and B using multiplication table M
SetProd := function(A,B,M)
  return Set(EnumeratorOfCartesianProduct([A,B]), p -> M[ p[1] ][ p[2] ]);
end;

# rm - relmorph defined as a list of image sets
IsRelMorph := function(rm, S, T)
  return ForAll(Tuples([1..Size(S)],2), # for all pairs in S
                p -> IsSubset(rm[S[ p[1] ][ p[2] ]], # the image of the product
                        SetProd(rm[ p[1] ],rm[ p[2] ],T))); #product of images
end;

# all possible relational morphisms
AllRelMorphs := function(S,T)
  local bitstrings, Tsubs, rms;
  # bitstrings describing all subsets of T (the enumerator is lazy)
  bitstrings := EnumeratorOfCartesianProduct(List([1..Size(T)],
                                                  x->[true,false]));
  Tsubs := Filtered(List(bitstrings,
                         x-> Filtered([1..Size(T)], y->x[y])),
                    x->Size(x)>0);
  rms := EnumeratorOfCartesianProduct(List([1..Size(S)],x->Tsubs));
  Info(SubSemiInfoClass,1, Size(Tsubs), " nonempty subsets in target");
  Info(SubSemiInfoClass,1, Size(rms), " possible relmorphs");
  return Filtered(rms, x->IsRelMorph(x,S,T));
end;

# all divisions
AllDivs := function(S,T)
  local partitions, L, f;
  #partitions of T with size not smaller than size of S
  partitions := Filtered(PartitionsSet([1..Size(T)]), x->Size(x)>=Size(S));
  #for each such partition, take combinations of its elements of size |S|
  #and produce all permutations of these
  f := function(part)
    local comb, result;
    result := [];
    for comb in IteratorOfCombinations(part, Size(S)) do
      Append(result, PermutationsList(comb));
    od;
    return result;
  end;
  L := Union(List(partitions,f));
  Info(SubSemiInfoClass,1, Size(L), " possible divisions");
  return Filtered(L, x->IsRelMorph(x,S,T));
end;

# invariant:
# IsSubset(AllRelMorphs(S,T), AllDivs(S,T));
# true
