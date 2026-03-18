(* ::Package:: *)

BeginPackage["CombinatoricsTools`", {"BooleanTools`"}];


spaceDimensions


RowKroneckerProduct
RowJoin


RaggedMultiIndex
ArrayMultiIndex


PivotColumns (*https://resources.wolframcloud.com/FunctionRepository/resources/PivotColumns/*)


WeakCompositions
ThinPartitions


ConjugatePartition (*https://resources.wolframcloud.com/FunctionRepository/resources/ConjugatePartition/*)
SchurS
SemiStandardYoungTableaux (*https://github.com/PerAlexandersson/Mathematica-packages*)


Begin["`Private`"];


(* ::Subsubsection:: *)
(*Public Functions*)


spaceDimensions[VectorSpaceBasis_List] := Total /@ Map[Times @@ #[["dimensions"]]&, VectorSpaceBasis, {2}]


RowKroneckerProduct[m1_List ? ArrayQ, {{{}}}] := {{}}
RowKroneckerProduct[{{{}}}, m2_List ? ArrayQ] := {{}}


RowKroneckerProduct[
 m1_?ArrayQ,
 m2_?ArrayQ
] /; Length @ m1 == Length @ m2 && Depth @ m1 == 4 == Depth @ m2 :=
 Flatten[
  MapThread[KroneckerProduct, {m1, m2}],
  {{1, 3}, {2}}
 ]


RowJoin[ms__] := Join[ms, 2]


RaggedMultiIndex[
 {},
 dimensions_?PositiveIntegersQ
] := {}


RaggedMultiIndex[
 linearIndices_?PositiveIntegersQ,
 dimensions_?PositiveIntegersQ
] /; Max @ linearIndices <= Total @ dimensions := 
 With[
  {accumulateDimensions = Prepend[Accumulate @ dimensions, 0]},
  {i = Flatten[FirstPosition[accumulateDimensions, total_ /; # <= total] & /@ linearIndices] - 1},
  {j = linearIndices - accumulateDimensions[[i]]},

  Transpose @ {i, j}
 ]


ArrayMultiIndex[
 linearIndex_?PositiveIntegerQ,
 dimensions_?PositiveIntegersQ
] /; linearIndex <= Times @@ dimensions :=
 IntegerDigits[linearIndex - 1, MixedRadix @ dimensions, Length @ dimensions] + 1


PivotColumns[matrix_?MatrixQ] :=
 Position[#, _?NonZeroQ, {1}, 1, Heads -> False] & /@ RowReduce[matrix, Tolerance -> 10^-12] // Flatten


WeakCompositions::usage = "gives a list of all weak integer compositions of D into n parts."


SetAttributes[WeakCompositions, Listable]


WeakCompositions[
 D_?NonNegativeIntegerQ,
 n_?PositiveIntegerQ
] :=
 Join @@ Permutations /@ IntegerPartitions[D, {n}, Range[0, D]]


ThinPartitions::usage = "gives a list of all integer partitions of d with parts at most Min[2\[Lambda]+1,m]."


SetAttributes[ThinPartitions, Listable]


ThinPartitions[
 d_?NonNegativeIntegerQ,
 \[Lambda]_?PositiveIntegerQ,
 m_?PositiveIntegerQ
] := 
 IntegerPartitions[d, All, Range[Min[2\[Lambda]+1, m]]]


ConjugatePartition::usage = "gives the integer partition conjugate to p."


ConjugatePartition[
 {}
] = {}


ConjugatePartition[
 p_?IntegerPartitionQ
] := 
 Total @ UnitStep @ Outer[Plus, p, -Range @ First @ p]


SchurS::usage = "gives the Schur polynomial corresponding to the integer partition p in the variables \!\(\*SuperscriptBox[\(q\), \(-\[Lambda]\)]\),...,\!\(\*SuperscriptBox[\(q\), \(\[Lambda]\)]\)."


SchurS[
 {},
 q_Symbol,
 \[Lambda]_?NonNegativeIntegerQ
] := 1


SchurS[
 p_?IntegerPartitionQ,
 q_Symbol,
 \[Lambda]_?NonNegativeIntegerQ
] := 
 q^(MacdonaldN @ p - \[Lambda] * Total @ p) * Times @@ ((1-q^(2\[Lambda]+1+Contents @ p))/(1-q^HookLengths @ p))


SemiStandardYoungTableaux::usage = "gives a list of all semistandard Young tableaux of shape p with largest entry n."


SemiStandardYoungTableaux[
 {},
 n_?PositiveIntegerQ
] := {{}}


SemiStandardYoungTableaux[
 p_?IntegerPartitionQ,
 n_?PositiveIntegerQ
] := 
 Join @@ SemiStandardYoungTableaux[p] /@ WeakCompositions[Tr @ p, n]


SemiStandardYoungTableaux[
 p_?IntegerPartitionQ][
 w_?NonNegativeIntegersQ
] := 
 SemiStandardYoungTableaux[p, w]


SemiStandardYoungTableaux[
 p_?IntegerPartitionQ,
 w_?NonNegativeIntegersQ
] := 
 With[
  {
   mu = ConstantArray[0, First @ p],
   mid = IntegerPartitions[#, {First @ p}, Range[0, Length @ p]] & /@ Most @ Accumulate @ w,
   cp = ConjugatePartition @ p
  },
  {
   partitionLevels = Join[{{mu}}, mid, {{cp}}]
  },
  {
   g = 
    Graph[
     Join @@ Table[
      Join @@ Outer[
       If[Min[#2-#1] >= 0 \[And] Min[#1[[;;-2]]-#2[[2;;]]] >= 0,
        DirectedEdge[{#1, lvl-1}, {#2, lvl}],
        Nothing
       ] &,
       partitionLevels[[lvl-1]],
       partitionLevels[[lvl]],
       1
      ],
      {lvl, 2, Length[partitionLevels]}
     ]
    ]
  },
  {
   vertices = VertexList @ g
  },
  {
   ssytPaths = If[
    Or[
     !MemberQ[vertices, {mu, 1}],
     !MemberQ[vertices, {cp, Length[w]+1}]
    ],
    {},
    FindPath[g, {mu, 1}, {cp, Length[w]+1}, Infinity, All]
   ]
  },

  N @ Map[
   Through[{Keys, Values}[Sort @ Counts @ #]] & /@ pathToSSYT[First /@ #] &,
   ssytPaths
  ]
 ]


(* ::Subsubsection:: *)
(*Private Functions*)


pathToSSYT[pathIn_List] := 
 With[
  {numRows = Length @ First @ pathIn},
  {path = Prepend[pathIn, ConstantArray[0, numRows]]},

  Table[
   Join @@ Table[
    ConstantArray[If[e-1 == 0, None, e-1], path[[e+1, r]]-path[[e, r]]],
    {e, Length @ pathIn}
   ],
   {r, numRows}
  ]
 ]


MacdonaldN[p_?IntegerPartitionQ] := p . Range[0, Length @ p-1]


Contents[p_?IntegerPartitionQ] := Flatten @ Table[j - i, {i, Length @ p}, {j, p[[i]]}]


HookLengths[p_?IntegerPartitionQ] := 
 With[
  {cp = ConjugatePartition @ p},
 
  Flatten @ Table[p[[i]] + cp[[j]] - i - j + 1, {i, Length @ p}, {j, p[[i]]}]
 ]


End[];


EndPackage[];
