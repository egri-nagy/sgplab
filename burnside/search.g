#creating Z5

#wreath Z5
#Z5Z5 := WreathProduct(Z5,Z5);
#Z5Z5Z5 := WreathProduct(Z5Z5,Z5);


#The function for checking some random samples whether the subgroup is 5-torsion i.e. g^5=1 for all g in G
Is5TorsionCandidateEndlessRandomCheck := function(G)
local i,c;
  Print("Checking random samples of group of order",Size(G),"\n");
  #Randomized test
  c:=0;
  Print("Checking random elements...");
  while (true) do
  for i in [1..1000000] do
    if Random(G)^5 <> () then
	Print("FAIL\n");
	return false;
    fi;
  od;
  c := c+1;
  Print(c,"millions of checks passed...\n");
  od;

end;


#The function for checking some random samples whether the subgroup is 5-torsion i.e. g^5=1 for all g in G
Is5TorsionCandidateRandomCheck := function(G,num_of_rand_checks)
local i;
  Print("Checking random samples of group of order",Size(G),"\n");
  #Randomized test
  Print("Checking random elements...");
  for i in [1..num_of_rand_checks] do
    if Random(G)^5 <> () then
	Print("FAIL\n");
	return false;
    fi;
  od;
  Print("GOOD random samples, further check is needed...\n");
  return true;
end;

#Checks only the generators
Is5TorsionCandidateGeneratorCheck := function(G)
local i;
  Print("Checking generators of group  with order ",Size(G),"\n");
  for i in GeneratorsOfGroup(G) do
    if i^5 <> () then
	Print("FAIL\n");
	return false;
    fi;
  od;
  Print("GOOD generators, further check is needed...\n");
  return true;
end;


#First checks the generators then some random elements
Is5TorsionCandidate := function(G)
Print("G\n");
  if not (Is5TorsionCandidateGeneratorCheck(G)) then return false;fi;
Print("R\n");
  if not (Is5TorsionCandidateRandomCheck(G,100000)) then return false;fi;
  return true; 
end;

#full check
Is5Torsion := function(G)
local i;
Print("FULL CHECK!\n\n",GeneratorsOfGroup(G),"\n\n");

  for i in G do
    if i^5 <> () then return false; fi;
  od;
  return true;
end;

#the main function here
SearchForMax5TorsionSubgroup := function(G)
local l,i,nl; #l - list, nl - new list

#We start with the maximal subgroups
l := [G];

#then it is a breadth-first search
while not IsEmpty(l) do
  nl := [];
  #sweeps
  for i in [1..Size(l)] do
    if Is5TorsionCandidate(l[i]) then
	if Is5Torsion(l[i]) then Print("SUCCESS!!!");return l[i];fi;
    else
	Print("Looking for max subgroup classes... in \n",l[i],"\n");
	Append(nl, MaximalSubgroupClassReps(l[i]));
    fi;	
  od;
  Print(Size(nl)," new groups");
  l := nl;
od;
Print("FAIL\n");
end;

# looking for subgroups of the group generated by gens, that are generated by two elements
CheckSubGroupsGeneratedBy2 := function(gens)
local indexlist,i,j,l,g;
#generating indexlist
  indexlist := [];
  for i in [1..(Size(gens)-1)] do
    for j in [i..Size(gens)] do
      Add(indexlist,[i,j]);
    od;
  od;
  #now trying all 2 generators
  for i in indexlist do
    l := [gens[i[1]],gens[i[2]]];
    g := GroupByGenerators(l);
    Print("generators",l," ");
    Print(Size(g),"\n\n");
  od;
end;