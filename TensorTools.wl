(* ::Package:: *)

BeginPackage["TensorTools`", {"CombinatoricsTools`", "BooleanTools`"}];


EvaluateTensorTrain
EvaluateAntisymmetrizedTensorTrain
EvaluateSymmetrizedTensorTrain
EvaluateYoungSymmetrizedTensorTree


Begin["`Private`"];


(* ::Subsubsection:: *)
(*Public Functions*)


EvaluateTensorTrain[
 {1},
 vectors_List
] :=
 First @ vectors


EvaluateAntisymmetrizedTensorTrain[
 {1},
 vectors_List
] :=
 First @ vectors


EvaluateSymmetrizedTensorTrain[
 {1},
 vector_List?VectorQ
] :=
 vector


EvaluateYoungSymmetrizedTensorTree[
 tensorTrees_Association,
 {{}},
 variables_List
] :=
 ConstantArray[{{{1.}}}, Length @ variables]


EvaluateTensorTrain[
 tt_List,
 vv_List
] :=
 Module[
  {acc = First @ vv},
  Do[
    acc = vv[[k + 1]] . (acc . tt[[k]]),
    {k, 1, Length @ tt}
  ];
  acc
]


(*assumes the first tensor factor is Antisymmetric[{1,2}]*)
EvaluateAntisymmetrizedTensorTrain[vectors_List][tensorTrain_List] := EvaluateAntisymmetrizedTensorTrain[tensorTrain, vectors]
EvaluateAntisymmetrizedTensorTrain[
 tensorTrain_List,
 vectors_List
] :=
  With[
   {data = AntisymmetrizationData[1 + Length @ tensorTrain]},
   
   (First @ data) . (EvaluateTensorTrain[tensorTrain, vectors[[#]]] & /@ Last @ data)
  ]


EvaluateSymmetrizedTensorTrain[
 tensorTrain_List,
 vector_List?VectorQ
] :=
 Fold[Dot[vector, Dot[#1, #2]] &, vector, tensorTrain]


(*variables; SSYTs; tensorTrees; vector*)
EvaluateYoungSymmetrizedTensorTree[
 tensorTrees_Association,
 SSYTs_List,
 variables_List
] :=
 Outer[
  Total[
   Outer[
    EvaluateAntisymmetrizedTensorTree[tensorTrees, {##}] &,
    Sequence @@ PartiallySymmetrizedMonomialCP[##],
    1
   ],
   Length @ First @ #2
  ] &,
  variables,
  SSYTs,
  1
 ]


(* ::Subsubsection:: *)
(*Private Functions*)


AntisymmetrizationData[d_?PositiveIntegerQ] :=
 AntisymmetrizationData[d] =
  With[
   {permutations = Select[Permutations @ Range @ d, #[[1]] < #[[2]] & ]},
   
   {Signature /@ permutations, permutations}
  ]


SymmetrizedMonomialCP[powers_List] :=
  SymmetrizedMonomialCP[powers] =
   With[
    {ds = ReplacePart[powers, 1 -> 0.], d = Total @ powers},
    {\[Zeta]s = Exp[(2\[Pi] * I) / (ds + 1)]},
    {grid = Tuples[\[Zeta]s^Range[0, ds]]},
    
    MapApply[Times, grid]^(1 / d) * grid
   ]


PartiallySymmetrizedMonomialCP[
 variables_List,
 SSYT_List
] :=
 MapThread[
  SymmetrizedMonomialCP[#2] . variables[[#1]] &,
  SSYT
 ]


EvaluateAntisymmetrizedTensorTree[
 tensorTrees_Association,
 vectors_List
] :=
 With[
  {interiorVectors = Map[EvaluateAntisymmetrizedTensorTrain[vectors], tensorTrees[["leafObjects"]], {2}]},
  
  MapThread[EvaluateTensorTrain, {tensorTrees[["interiorTensorTrains"]], interiorVectors}]
 ]


End[];


EndPackage[];
