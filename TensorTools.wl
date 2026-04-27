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


(*vector*)
EvaluateCore[
 v1_,
 v2_,
 core_,
 modulus_?NonNegativeIntegerQ
] :=
 DotMod[modulus][v2, DotMod[modulus][v1, core]]


(*batch; ...; batch; vector*)
BatchEvaluateCore[
 v1Batch_,
 v2Batch_,
 core_,
 modulus_?NonNegativeIntegerQ
] :=
 ModReduce[modulus] @ Total[
  ArrayReshape[
   v2Batch, (*this assumes that v1Batch always has at least as many axes as v2Batch, which should be the case for us*)
   Join[
    {First @ Dimensions @ v2Batch},
    ConstantArray[1, ArrayDepth @ v1Batch - ArrayDepth @ v2Batch],(*This doesn't work since Mathematica can't broadcast*)
    Rest @ Dimensions @ v2Batch
   ]
  ] * DotMod[modulus][v1Batch, core],
  {ArrayDepth @ v1Batch}
 ]


(*batch 2; batch 1; vector*)
MultiBatchEvaluateCore[
 v1MultiBatch_,
 v2MultiBatch_,
 core_,
 modulus_?NonNegativeIntegerQ
] :=
 ModReduce[modulus] @ ArrayDot[
  v2MultiBatch,
  DotMod[modulus][v1MultiBatch, core],
  {{ArrayDepth @ v2MultiBatch, ArrayDepth @ v1MultiBatch}}
 ]


(*batch; batch 2; batch 1; vector*)
BatchMultiBatchEvaluateCore[
 v1BatchMultiBatch_,
 v2BatchMultiBatch_,
 core_,
 modulus_?NonNegativeIntegerQ
] :=
 MapThread[
  MultiBatchEvaluateCore[#1, #2, core, modulus] &,
  {v1BatchMultiBatch, v2BatchMultiBatch}
 ]


(* ::Subsubsection:: *)
(*EvaluateTensorTrain*)


EvaluateTensorTrain[
 cores_List,
 vectors_List,
 modulus_?NonNegativeIntegerQ,
 f_
] :=
 Fold[
  f[#1, vectors[[#2 + 1]], cores[[#2]], modulus] &,
  vectors[[1]],
  Range @ Length @ cores
 ]


EvaluateTensorTrain[
 cores_List,
 vectors_List,
 modulus_?NonNegativeIntegerQ,
 f_,
 perm_
] :=
 ReorderMultiBatchAxes[
  Fold[
   f[#1, vectors[[perm[[#2 + 1]]]], cores[[#2]], modulus] &,
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
 Module[
  {n, reverse, axisPerm},

  n = Length @ perm;
  reverse = Range[n, 1, -1];
  axisPerm = InversePermutation @ PermutationProduct[reverse, InversePermutation @ perm, reverse];

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
 modulus_?NonNegativeIntegerQ,
 f_
] :=
 Fold[
  f[#1, vector, #2, modulus] &,
  vector,
  cores
 ]


(* ::Subsubsection:: *)
(*EvaluateAntisymmetrizedTensorTrain*)


EvaluateAntisymmetrizedTensorTrain[
 cores_List,
 vectors_List,
 modulus_?NonNegativeIntegerQ,
 f_
] :=
 ModReduce[modulus] @ Sum[
  i[[1]] * EvaluateTensorTrain[cores, vectors, modulus, f, i[[2]]],
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
 modulus_?NonNegativeIntegerQ
] :=
 ConstantArray[{1}, (Dimensions @ probeBatches)[[2]]]


EvaluateYoungSymmetrizedTensorTree[
 tensorTree_Association,
 SSYT_List,
 probeBatches_List,
 modulus_?NonNegativeIntegerQ
] :=
 Module[
  {grids, vars, sym, antisym, final},

  (*SSYT column; CP summands; distinct variables*)
  grids = SymmetrizedMonomialCP[#, modulus] & /@ Last @ SSYT;

  (*SSYT column; distinct variables; random probe; vector*)
  vars = probeBatches[[#]] & /@ First @ SSYT;

  (*SSYT column; random probe; CP summands; vector*)
  sym = Transpose /@ MapThread[DotMod[modulus], {grids, vars}];

  (*part of partition; random probe; CP summands column c; ...; CP summands column 1; vector*)
  antisym = EvaluateAntisymmetrizedTensorTrain[#, sym, modulus, BatchMultiBatchEvaluateCore] & /@ tensorTree[["leafTensorTrains"]];

  (*random probe; CP summands column c; ...; CP summands column 1; vector*)
  final = EvaluateTensorTrain[tensorTree[["interiorTensorTrain"]], antisym, modulus, BatchEvaluateCore];

  (*random probe; vector*)
  Fold[ModReduce[modulus] @ ArrayDot[#1, #2, {{2, 1}}] &, final, Reverse @ ModReduce[modulus] @ Apply[Times, grids, {2}]]
 ]


(*CP summands; multiplicity*)
SymmetrizedMonomialCP[powers_?PositiveIntegersQ, modulus_?NonNegativeIntegerQ] :=
 SymmetrizedMonomialCP[powers, modulus] =
  Module[
   {ds, \[Zeta]s},

   ds = ReplacePart[powers, 1 -> 0];
   \[Zeta]s = If[modulus == 0, Exp[2 \[Pi] I / (ds + 1)], PowerMod[PrimitiveRoot @ modulus, (modulus - 1) / (ds + 1), modulus]];

   Developer`ToPackedArray @ Tuples @ PowerMod[\[Zeta]s, Range[0, ds], modulus]
  ]


End[];


EndPackage[];
