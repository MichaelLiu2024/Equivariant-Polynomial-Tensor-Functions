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
ConjugateTableau (*https://resources.wolframcloud.com/FunctionRepository/resources/TransposeTableau/*)
SchurS
SemiStandardYoungTableaux


Begin["`Private`"];


(* ::Subsubsection:: *)
(*Public Functions*)


spaceDimensions[VectorSpaceBasis_List] := Total /@ Map[Times @@ #[["dimensions"]] &, VectorSpaceBasis, {2}]


RowKroneckerProduct[
 m1_List ? ArrayQ,
 {{{}}}
] :=
 {{}}
RowKroneckerProduct[
 {{{}}},
 m2_List ? ArrayQ
] :=
 {{}}


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
 IntegerPartitions[d, All, Range[Min[2\[Lambda] + 1, m]]]


ConjugatePartition::usage = "gives the integer partition conjugate to p."


ConjugatePartition[{}] = {}


ConjugatePartition[p_?IntegerPartitionQ] := Total @ UnitStep @ Outer[Plus, p, -Range @ First @ p]


ConjugateTableau[{{}}] = {{}}


ConjugateTableau[tableau_List] := Flatten[tableau, {{2}, {1}}]


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
 q^(MacdonaldN @ p - \[Lambda] * Total @ p) * Times @@ ((1 - q^(2\[Lambda] + 1 + Contents @ p)) / (1 - q^HookLengths @ p))


SemiStandardYoungTableaux::usage = "gives a list of all semistandard Young tableaux of shape p with largest entry m."


SemiStandardYoungTableaux[
 {},
 m_?PositiveIntegerQ
] := {{}}


SemiStandardYoungTableaux[
 p_?IntegerPartitionQ,
 m_?PositiveIntegerQ
] :=
 N @ Transpose[Through[{Keys, Values}[Sort @ Counts @ #]] & /@ #] & /@ ConjugateTableau /@ With[
  {v = Array[x, Total @ p]},
  {rows = TakeList[v, p]},
  {
   constraints =
    And @@ Flatten[
     {
      Thread[1 <= v <= m],
      Thread[Most[#] < Rest[#]] & /@ rows,
      Thread[Most[#] <= Rest[#]] & /@ ConjugateTableau @ rows
     }
    ]
  },
  
  TakeList[#, p] & /@ SolveValues[constraints, v, Integers]
 ]


(* ::Subsubsection:: *)
(*Private Functions*)


MacdonaldN[p_?IntegerPartitionQ] := p . Range[0, Length @ p - 1]


Contents[p_?IntegerPartitionQ] := Flatten @ Table[j - i, {i, Length @ p}, {j, p[[i]]}]


HookLengths[p_?IntegerPartitionQ] :=
 With[
  {cp = ConjugatePartition @ p},
 
  Flatten @ Table[p[[i]] + cp[[j]] - i - j + 1, {i, Length @ p}, {j, p[[i]]}]
 ]


End[];


EndPackage[];
