(* ::Package:: *)

BeginPackage["TensorTools`", {"CombinatoricsTools`", "BooleanTools`"}];


EvaluateCore
BatchEvaluateCore
MultiBatchEvaluateCore
BatchMultiBatchEvaluateCore


EvaluateTensorTrain
EvaluateSymmetrizedTensorTrain
EvaluateAntisymmetrizedTensorTrain


EvaluateYoungSymmetrizedTensorTree


Begin["`Private`"];


(* ::Subsubsection:: *)
(*EvaluateCore, BatchEvaluateCore, MultiBatchEvaluateCore, BatchMultiBatchEvaluateCore*)


DotMod[0] := Dot
DotMod[p_?PrimeQ] := Mod[Dot[##], p] &


(*vector*)
EvaluateCore[
 v1_,
 v2_,
 core_
] :=
 v2 . (v1 . core)


(*batch; ...; batch; vector*)
BatchEvaluateCore[
 v1Batch_,
 v2Batch_,
 core_
] :=
 Total[
  ArrayReshape[
   v2Batch, (*this assumes that v1Batch always has at least as many axes as v2Batch, which should be the case for us*)
   Join[
    {First @ Dimensions @ v2Batch},
    ConstantArray[1, ArrayDepth @ v1Batch - ArrayDepth @ v2Batch],
    Rest @ Dimensions @ v2Batch
   ]
  ] * v1Batch . core,
  {ArrayDepth @ v1Batch}
 ]


(*batch 2; batch 1; vector*)
MultiBatchEvaluateCore[
 v1MultiBatch_,
 v2MultiBatch_,
 core_
] :=
 ArrayDot[v2MultiBatch, v1MultiBatch . core, {{ArrayDepth @ v2MultiBatch, ArrayDepth @ v1MultiBatch}}]


(*batch; batch 2; batch 1; vector*)
BatchMultiBatchEvaluateCore[
 v1BatchMultiBatch_,
 v2BatchMultiBatch_,
 core_
] :=
 MapThread[MultiBatchEvaluateCore[#1, #2, core] &, {v1BatchMultiBatch, v2BatchMultiBatch}]


(* ::Subsubsection:: *)
(*EvaluateTensorTrain*)


EvaluateTensorTrain[
 cores_List,
 vectors_List,
 char_,
 f_
] :=
 Fold[
  f[#1, vectors[[#2 + 1]], cores[[#2]]] &,
  vectors[[1]],
  Range @ Length @ cores
 ]


EvaluateTensorTrain[
 cores_List,
 vectors_List,
 char_,
 f_,
 perm_
] :=
 ReorderMultiBatchAxes[
  Fold[
   f[#1, vectors[[perm[[#2 + 1]]]], cores[[#2]]] &,
   vectors[[perm[[1]]]],
   Range @ Length @ cores
  ],
  f,
  perm
 ]


ReorderMultiBatchAxes[
 result_,
 f_,
 perm_
] :=
 With[
  {n = Length @ perm},
  {reverse = Range[n, 1, -1]},
  {axisPerm = InversePermutation @ PermutationProduct[reverse, InversePermutation @ perm, reverse]},
  
  If[n <= 1, Return @ result];
  
  Switch[
    f,
    
    MultiBatchEvaluateCore,
    Transpose[result, Append[axisPerm, n + 1]],

    BatchMultiBatchEvaluateCore,
    Transpose[result, Join[{1}, 1 + axisPerm, {n + 2}]],
    
    _,
    result
   ]
 ]


(* ::Subsubsection:: *)
(*EvaluateSymmetrizedTensorTrain*)


EvaluateSymmetrizedTensorTrain[
 cores_List,
 vector_List,
 f_
] :=
 Fold[
  f[#1, vector, #2] &,
  vector,
  cores
 ]


(* ::Subsubsection:: *)
(*EvaluateAntisymmetrizedTensorTrain*)


EvaluateAntisymmetrizedTensorTrain[
 cores_List,
 vectors_List,
 f_
] :=
 Sum[
  i[[1]] * EvaluateTensorTrain[cores, vectors, f, i[[2]]],
  {i, AntisymmetrizationData[Length @ cores + 1]}
 ]


AntisymmetrizationData[1] := {{1, {1}}}
AntisymmetrizationData[d_?PositiveIntegerQ] :=
 AntisymmetrizationData[d] =
  With[
   {perms = Select[Permutations @ Range @ d, #[[1]] < #[[2]] &]}, (*assume that the first core is Antisymmetric[{1, 2}]*)
   
   Transpose @ {Signature /@ perms, perms}
  ]


(* ::Subsubsection:: *)
(*YoungSymmetrizedTensorTree*)


EvaluateYoungSymmetrizedTensorTree[
 tensorTree_Association,
 {},
 probeBatches_List,
 char_?NonNegativeIntegerQ
] :=
 ConstantArray[{1}, Dimensions[probeBatches][[2]]]


EvaluateYoungSymmetrizedTensorTree[
 tensorTree_Association,
 SSYT_List,
 probeBatches_List,
 char_?NonNegativeIntegerQ
] :=
 With[
  {
   (*SSYT column; CP summands; distinct variables*)
   grids = SymmetrizedMonomialCP[#, char] & /@ Last @ SSYT,
   
   (*SSYT column; distinct variables; random probe; vector*)
   vars = probeBatches[[#]] & /@ First @ SSYT
  },
  {
   (*SSYT column; random probe; CP summands; vector*)
   sym = Transpose /@ MapThread[DotMod[char], {grids, vars}]
  },
  {
   (*part of partition; random probe; CP summands column c; ...; CP summands column 1; vector*)
   antisym = EvaluateAntisymmetrizedTensorTrain[#, sym, BatchMultiBatchEvaluateCore] & /@ tensorTree[["leafTensorTrains"]]
  },
  {
   (*random probe; CP summands column c; ...; CP summands column 1; vector*)
   final = EvaluateTensorTrain[tensorTree[["interiorTensorTrain"]], antisym, BatchEvaluateCore]
  },
  
  (*random probe; vector*)
  Fold[ArrayDot[#1, #2, {{2, 1}}] &, final, Reverse @ Apply[Times, grids, {2}]]
 ]


(*CP summands; multiplicity*)
SymmetrizedMonomialCP[powers_?PositiveIntegersQ, char_?NonNegativeIntegerQ] :=
 SymmetrizedMonomialCP[powers, char] =
  With[
   {ds = ReplacePart[powers, 1 -> 0]},
   {\[Zeta]s = FieldRoot[ds + 1, char]},
   
   Developer`ToPackedArray @ Mod[Tuples[\[Zeta]s ^ Range[0, ds]], char]
  ]


SetAttributes[FieldRoot, Listable]
FieldRoot[d_?PositiveIntegerQ, char_?NonNegativeIntegerQ] :=
 Switch[
  char,
  
  0, Exp[2 \[Pi] I / d],
  
  _?PrimeQ, PowerMod[PrimitiveRoot @ char, (char - 1) / d, char]
 ]


End[];


EndPackage[];
