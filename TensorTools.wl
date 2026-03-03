(* ::Package:: *)

BeginPackage["TensorTools`", {"CombinatoricsTools`"}];


EvaluateTensorTrain
EvaluateSymmetrizedTensorTrain
EvaluateAntisymmetrizedTensorTrain
EvaluateAntisymmetrizedTensorTree
EvaluateYoungSymmetrizedTensorTree


Begin["`Private`"];


(* ::Subsubsection:: *)
(*Private Function Implementations*)


ContractVectors[
 vector1_,
 {vector2_, tensor_}
] :=


Dot[vector2, Dot[vector1, tensor]]


(* ::Subsubsection:: *)
(*Public Function Implementations*)


EvaluateTensorTrain[
 {1},
 vectors_List
] :=


First @ vectors


EvaluateTensorTrain[
 tensorTrain_List,
 vectors_List
] :=


Fold[ContractVectors, First @ vectors, Transpose[{vectors[[2 ;; 1 + Length @ tensorTrain]], tensorTrain}]]


EvaluateAntisymmetrizedTensorTrain[
 tensorTrain_List,
 vectors_List
] :=


With[
 {
  d = Length @ vectors,
  dim = Length @ First @ vectors
 },
 If[
  d <= dim,
  Plus @@ Signature /@ Permutations[d] *
   EvaluateTensorTrain[tensorTrain, vectors[[#]]] & /@ Permutations @ Range @ d,
  ConstantArray[0., 2 Last @ Dimensions @ Last @ tensorTrain + 1]
 ]
]


EvaluateSymmetrizedTensorTrain[
 tensorTrain_List,
 vector_List?VectorQ
] :=


With[
 {d = Length @ tensorTrain + 1},
 EvaluateTensorTrain[tensorTrain, ConstantArray[vector, d]]
]


EvaluateAntisymmetrizedTensorTree[
 tensorTrees_Association,
 vectors_List
] :=


MapApply[
 EvaluateAntisymmetrizedTensorTrain,
 {tensorTrees["leafObjects"], tensorTrees["interiorTensorTrains"]}
]


SymmetrizedMonomialCP[
 powers_List
]  /;  VectorQ[powers, Positive] :=


With[
 {
  perm = Range @ Total @ powers,
  cp = ConjugatePartition @ powers,
  p = PositionIndex[Total @ UnitStep @ Outer[Plus, powers, -Range @ First @ powers]],
  l = ConstantArray[Length @ powers, Total @ powers]
 },
 Product[
  Cycles[{{perm[[First @ p[[i]]]], perm[[#]]} & /@ p[[i, 2 ;;]]}] @ l,
  {i, Length @ cp}
 ]
]


SymmetrizedMonomialCP[
 variables_List,
 powers_List
] :=


With[
 {
  p = Flatten[MapThread[ConstantArray, {Range @ Length @ powers, powers}]],
  n = Length @ variables
 },
 If[
  Total @ powers == 0,
  1,
  (SymmetrizedMonomialCP[powers] @ variables[[#]]) &[
   ReplaceAll[p, Rule @@@ Thread[Range[n] -> Ordering[p]]]
  ]
 ]
]


PartiallySymmetrizedMonomialCP[
 variables_List,
 SSYT_List
] :=


Times @@ Map[SymmetrizedMonomialCP[variables, #] &, Values @ Sort @ GroupBy[SSYT, Last -> First], {2}]


EvaluateYoungSymmetrizedTensorTree[
 tensorTrees_Association,
 SSYTs_List,
 variables_List
] :=


With[
 {interiorVectors = PartiallySymmetrizedMonomialCP[variables, #] & /@ SSYTs},
 Dot[interiorVectors, EvaluateAntisymmetrizedTensorTree[tensorTrees, variables]]
]


End[];


EndPackage[];
