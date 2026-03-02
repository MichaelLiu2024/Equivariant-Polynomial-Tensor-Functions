(* ::Package:: *)

BeginPackage["CombinatoricsTools`"];


linearIndicesToRaggedMultiIndices
linearIndexToArrayMultiIndex
PositiveIntegerQ
NonNegativeIntegerQ
PivotColumns
IteratedSum
WeakCompositions
ThinPartitions
ConjugateTableau
ConjugatePartition
SchurS
SemiStandardYoungTableaux


Begin["`Private`"];


(* ::Subsubsection:: *)
(*Private Functions*)


pathToSSYT[pathIn_List]:=
 With[
  {m=Length@pathIn,numRows=Length@First@pathIn},
  {path=Prepend[pathIn,ConstantArray[0,numRows]]},
  
  Table[
   Join@@Table[
    ConstantArray[If[e-1==0,None,e-1],path[[e+1,r]]-path[[e,r]]],
    {e,m}
   ],
   {r,numRows}
  ]
 ];


MacdonaldN[p_List?VectorQ]:=p . Range[0,Length@p-1]


Contents[p_List?VectorQ]:=Flatten@Table[j-i,{i,Length@p},{j,p[[i]]}]


HookLengths[p_List?VectorQ]:=
 With[
  {cp=ConjugatePartition@p},
  Flatten@Table[p[[i]]+cp[[j]]-i-j+1,{i,Length@p},{j,p[[i]]}]
 ]


(* ::Subsubsection:: *)
(*Public Functions*)


linearIndicesToRaggedMultiIndices[{},dimensions_List?VectorQ]:={}
linearIndicesToRaggedMultiIndices[linearIndices_List?VectorQ,dimensions_List?VectorQ]/;Max@linearIndices<=Total@dimensions:=
 With[
  {accumulateDimensions=Prepend[Accumulate@dimensions,0]},
  {i=Flatten[FirstPosition[accumulateDimensions,total_/;#<=total]&/@linearIndices]-1},
  {j=linearIndices-accumulateDimensions[[i]]},
  
  Transpose@{i,j}
 ]


linearIndexToArrayMultiIndex[linearIndex_Integer?Positive,dimensions_List?VectorQ]/;linearIndex<=Times@@dimensions:=
 IntegerDigits[linearIndex-1,MixedRadix@dimensions,Length@dimensions]+1


PositiveIntegerQ[n_]:=Positive@n\[And]IntegerQ@n


NonNegativeIntegerQ[n_]:=NonNegative@n\[And]IntegerQ@n


(*https://resources.wolframcloud.com/FunctionRepository/resources/PivotColumns/*)
PivotColumns[matrix_?MatrixQ]:=Flatten@Map[Position[#,_?(#!=0&),{1},1,Heads->False]&,RowReduce[matrix,Tolerance->10^-10]]


IteratedSum[f_,ls_List]:=With[{vars=Unique@x&/@ls},Sum[f@@vars,Evaluate[Sequence@@Transpose@{vars,ls}]]]


WeakCompositions::usage="gives a list of all weak integer compositions of D into n parts."
SetAttributes[WeakCompositions,Listable]
WeakCompositions[D_Integer?NonNegative,n_Integer?Positive]:=Join@@Permutations/@IntegerPartitions[D,{n},Range[0,D]]


ThinPartitions::usage="gives a list of all integer partitions of d with parts at most Min[2\[Lambda]+1,m]."
SetAttributes[ThinPartitions,Listable]
ThinPartitions[d_Integer?NonNegative,\[Lambda]_Integer?Positive,m_Integer?Positive]:=IntegerPartitions[d,All,Range[Min[2\[Lambda]+1,m]]]


StandardYoungTableau::usage="gives the standard Young tableau of shape p filled in English reading order."
StandardYoungTableau[p_List?VectorQ]:=TakeList[Range@Total@p,p]


ConjugateTableau::usage="gives the Young tableau conjugate to t."
ConjugateTableau[t_List]:=Flatten[t,{2}]


(*https://resources.wolframcloud.com/FunctionRepository/resources/ConjugatePartition/*)
ConjugatePartition::usage="gives the integer partition conjugate to p."
ConjugatePartition[{}]={}
ConjugatePartition[p_List?VectorQ]:=Total@UnitStep@Outer[Plus,p,-Range@First@p]


SchurS::usage="gives the Schur polynomial corresponding to the integer partition p in the variables \!\(\*SuperscriptBox[\(q\), \(-\[Lambda]\)]\),...,\!\(\*SuperscriptBox[\(q\), \(\[Lambda]\)]\)."
SchurS[{},q_Symbol,\[Lambda]_Integer?NonNegative]:=1
SchurS[p_List?VectorQ,q_Symbol,\[Lambda]_Integer?NonNegative]:=q^(MacdonaldN@p-\[Lambda]*Total@p)*Times@@((1-q^(2\[Lambda]+1+Contents@p))/(1-q^HookLengths@p))


(*https://github.com/PerAlexandersson/Mathematica-packages*)
SemiStandardYoungTableaux::usage="gives a list of all semistandard Young tableaux of shape p with largest entry n."

SemiStandardYoungTableaux[{},n_Integer?Positive]:={{}}

SemiStandardYoungTableaux[p_List?VectorQ,n_Integer?Positive]:=Join@@SemiStandardYoungTableaux[p]/@WeakCompositions[Tr@p,n]

SemiStandardYoungTableaux[p_List?VectorQ][w_List?VectorQ]:=SemiStandardYoungTableaux[p,w]

SemiStandardYoungTableaux[p_List?VectorQ,w_List?VectorQ]:=
 With[
  {
   mu=ConstantArray[0,First@p],
   mid=IntegerPartitions[#,{First@p},Range[0,Length@p]]&/@Most@Accumulate@w,
   cp=ConjugatePartition@p
  },
  {
   partitionLevels=Join[{{mu}},mid,{{cp}}]
  },
  {
   g=
    Graph[
     Join@@Table[
      Join@@Outer[
       If[Min[#2-#1]>=0&&Min[#1[[;;-2]]-#2[[2;;]]]>=0,DirectedEdge[{#1,lvl-1},{#2,lvl}],Nothing]&,
       partitionLevels[[lvl-1]],
       partitionLevels[[lvl]],
       1
      ],
      {lvl,2,Length[partitionLevels]}
     ]
    ]
  },
  {
   ssytPaths=If[
    Or[!MemberQ[VertexList[g],{mu,1}],!MemberQ[VertexList[g],{cp,Length[w]+1}]],
    {},
    FindPath[g,{mu,1},{cp,Length[w]+1},Infinity,All]
   ]
  },
  
  N@Map[
   Through[{Keys,Values}[Sort@Counts@#]]&/@pathToSSYT[First/@#]&,
   ssytPaths
  ]
 ];


End[];


EndPackage[];
