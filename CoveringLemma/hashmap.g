# Relations represented as set-valued hash-maps, using the HashMap
# from the datastructures package.
# The only extra assumption is that the values are collections (sets).
# Naming: HashMapRelation is a relation represented by a set-valued HashMap.
# generic variable name: hmr

# given a relation hmr this returns all the distinct elements from
# all image sets
ImageOfHashMapRelation := function(hmr)
  return AsSet(Concatenation(AsSet(Values(hmr))));
end;

# turning around a hashmap
InvertHashMapRelation := function(hmr)
  local m;
  #putting in all values as keys with empty value set for now
  m := HashMap(List(ImageOfHashMapRelation(hmr),
                    x -> [x,[]]));
  Perform(Keys(hmr),
         function(k)
           Perform(hmr[k], #we put all related elements into the mutable lists
                  function(v)
                    AddSet(m[v], k);
                  end);
         end);
  return m;
end;

# it is injective if the inverse has singletons, i.e. the preimages are singletons
IsInjectiveHashMap := function(rel)
  return ForAll(Values(InvertHashMapRelation(rel)), coll -> Size(coll) = 1);
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

# just a quick check for hashmap equality
# it may miss list equality for values (if not sorted)
HashMapEq := function(m1, m2)
  return (AsSet(Keys(m1)) = AsSet(Keys(m2)))
         and
         ForAll(Keys(m1), k -> m1[k]=m2[k]);
end;
