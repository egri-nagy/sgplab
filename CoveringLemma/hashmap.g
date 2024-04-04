# Added functionality to HashMap from the datastructures package.

# given a set-valued hashmap m this returns all the distince elements from
# all image sets
DistinctValueElements := function(m)
  return AsSet(Concatenation(AsSet(Keys(m))));
end;

# turning around a hashmap
InvertHashMap := function(rel)
  local m;
  #putting in all values as keys with empty value set for now
  m := HashMap(List(DistinctElts(Values(rel)),
                    x -> [x,[]]));
  Perform(Keys(rel),
         function(k)
           Perform(rel[k], #we put all related elements into the mutable lists
                  function(v)
                    AddSet(m[v], k);
                  end);
         end);
  return m;
end;

# it is injective if the inverse has singletons, i.e. the preimages are singletons
IsInjectiveHashMap := function(rel)
  return ForAll(Values(InvertHashMap(rel)), coll -> Size(coll) = 1);
end;

#doing it a bit more efficiently, to see if there is any overlap between the image
# sets we have seen so far
IsInjectiveHashMap2 := function(rel)
  local coll,imgs;
  coll := [];
  for imgs in Values(rel) do
    if not IsEmpty(Intersection(coll,imgs)) then
      return false; #not injective
    fi;
    coll := Union(coll, imgs); #collect all the elements so far
  od;
  return true; #there was no overlap, so it is injective
end;

# classifying a collection based on the output of a function
# the output of the function is the key and value is the collection of elts
# producing that value
Classify := function(elts, f)
  local e, #an elemenet from elts
        d, #data constructed from e, f(e)
        m; #hashmap for the final result
  m := HashMap();
  for e in elts do
    d := f(e);
    if d in m then
      Add(m[d], e);
    else
      m[d] := [e];
    fi;
  od;
  return m;
end;

# the graph of a relation, i.e. all related pairs
HashMapGraph := function(rel)
  return Concatenation(List(Keys(rel),
                            k -> List(rel[k],
                                      v -> [k,v])));
end;

# creates a new set-valued hashmap using the same keys but with empty value sets
EmptyClone := function(hashmap)
  return HashMap(List(Keys(hashmap),
                      key -> [key, []]));
end;

# just a quick check for hashmap equality
# it may miss list equality for values (if not sorted)
HashMapEq := function(m1, m2)
  return (AsSet(Keys(m1)) = AsSet(Keys(m2)))
         and
         ForAll(Keys(m1), k -> m1[k]=m2[k]);
end;
