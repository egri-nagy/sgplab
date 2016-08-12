ip := function(n)
  local points, tuples;
  points := [1..n];
  tuples := EnumeratorOfCartesianProduct(ListWithIdenticalEntries(n,points)); #faster than EnumeratorOfTuples
  return Set(tuples, x->IndexPeriodOfTransformation(Transformation(x)));
end;
