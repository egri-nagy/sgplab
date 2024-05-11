# n degree, k rank
NumOfRankkTransformations := function(n,k)
  return Stirling2(n,k) * (Factorial(n)/Factorial(n-k));end;

NumOfLifts := function (n)
  return Factorial(n)
         + Sum(List([1..n-1],
                    k -> (n-k) * NumOfRankkTransformations(n,k)));
end;
