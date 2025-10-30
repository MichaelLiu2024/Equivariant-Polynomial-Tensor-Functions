(* ::Package:: *)

(* ::Section:: *)
(*Public Functions*)


BeginPackage["CombinatoricsTools`"];


(* ::Subsection:: *)
(*Public Function Declarations*)


(*https://resources.wolframcloud.com/FunctionRepository/resources/SchurS*)
SchurS::usage="gives the Schur polynomial corresponding to the integer partition p in the variables x1,\[Ellipsis],xn."


StrictCompositions::usage="returns a List of all strict integer compositions of D with n parts"


WeakCompositions::usage="returns a List of all weak integer compositions of D with n parts"


ThinPartitions::usage="returns a List of all integer partitions of d with parts at most Min[2\[Lambda]+1,m]"


YoungTableau::usage="returns the standard Young tableau of shape p with boxes filled increasingly in English reading order"


ConjugateTableau::usage="returns the Young tableau conjugate to t"


(*https://resources.wolframcloud.com/FunctionRepository/resources/ConjugatePartition/*)
ConjugatePartition::usage="returns the integer partition conjugate to p"


(*https://github.com/PerAlexandersson/Mathematica-packages*)
SemiStandardYoungTableaux::usage="returns a List of all semistandard Young tableaux of shape p with boxes filled from Range[n]"


(* ::Section:: *)
(*Private Functions*)


Begin["`Private`"];


(* ::Subsection:: *)
(*Private Function Attributes*)


SetAttributes[
{
StrictCompositions,
WeakCompositions,
ThinPartitions
},
Listable
]


(* ::Subsection:: *)
(*Public Function Implementations*)


SchurS=ResourceFunction["SchurS"];


StrictCompositions[D_Integer?NonNegative,n_Integer?Positive]:=Join@@Permutations/@IntegerPartitions[D,{n}]


WeakCompositions[D_Integer?NonNegative,n_Integer?Positive]:=Join@@Permutations/@IntegerPartitions[D,{n},Range[0,D]]


ThinPartitions[d_Integer?NonNegative,\[Lambda]_Integer?NonNegative,m_Integer?Positive]:=IntegerPartitions[d,All,Range[Min[2\[Lambda]+1,m]]]


YoungTableau[p_List?VectorQ]:=TakeList[Range[Total[p]],p]


ConjugateTableau[t_List]:=Flatten[t,{2}]


ConjugatePartition[p_List?VectorQ]:=Total[UnitStep[Outer[Plus,p,-Range[First[p]]]]]


SemiStandardYoungTableaux[p_List?VectorQ,n_Integer?Positive]:=Join@@Table[SemiStandardYoungTableaux[p,w],{w,WeakCompositions[Tr[p],n]}]


SemiStandardYoungTableaux[pp_List,w_List]:=
Module[
{p,partitionLevels,directedEdges,mid,mu,ssytPaths,g,pathToSSYT},

p=ConjugatePartition[pp];

mu=ConstantArray[0,Length[p]];

mid=Table[IntegerPartitions[wi,{Length[p]},Range[0,Max[p]]],{wi,Most[Accumulate[w]]}];

partitionLevels=Join[{{mu}},mid,{{p}}];

directedEdges=
Join@@Table[
Join@@Outer[
If[Min[#2-#1]>=0&&Min[#1[[;;-2]]-#2[[2;;]]]>=0,DirectedEdge[{#1,lvl-1},{#2,lvl}],Nothing]&,
partitionLevels[[lvl-1]],partitionLevels[[lvl]],1
],
{lvl,2,Length[partitionLevels]}
];

g=Graph[directedEdges];

ssytPaths=
If[
Or[!MemberQ[VertexList[g],{mu,1}],!MemberQ[VertexList[g],{p,Length[w]+1}]],
{},
FindPath[g,{mu,1},{p,Length[w]+1},Infinity,All]
];

pathToSSYT[pathIn_List]:=
Module[
{path,nrows,m},

{m,nrows}=Dimensions[pathIn];

path=Prepend[pathIn,ConstantArray[0,nrows]];

Table[Join@@Table[ConstantArray[If[e-1==0,None,e-1],path[[e+1,r]]-path[[e,r]]],{e,m}],{r,nrows}]];

Map[ConjugateTableau[pathToSSYT[First/@#]]&,ssytPaths]
];


End[];


EndPackage[];
