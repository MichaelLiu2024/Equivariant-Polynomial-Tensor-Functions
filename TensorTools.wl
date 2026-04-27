(* ::Package:: *)

BeginPackage["TensorTools`", {"CombinatoricsTools`", "BooleanTools`"}];


ClebschGordanTensor


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
(*ClebschGordanTensor*)


UnitaryClebschGordanTensor[{\[Lambda]1_?NonNegativeIntegerQ, \[Lambda]2_?NonNegativeIntegerQ, \[Lambda]3_?NonNegativeIntegerQ}] :=
 UnitaryClebschGordanTensor[{\[Lambda]1, \[Lambda]2, \[Lambda]3}] =
  Module[
   {out = ConstantArray[0., {2\[Lambda]1 + 1, 2\[Lambda]2 + 1, 2\[Lambda]3 + 1}]},

   Do[
    out[[1 + \[Lambda]1 + m1, 1 + \[Lambda]2 + m2, 1 + \[Lambda]3 + m1 + m2]] = N @ ClebschGordan[{\[Lambda]1, m1}, {\[Lambda]2, m2}, {\[Lambda]3, m1 + m2}],
    {m1, -\[Lambda]1, \[Lambda]1},
    {m2, Max[-\[Lambda]2, -\[Lambda]3 - m1], Min[\[Lambda]2, \[Lambda]3 - m1]}
   ];

   Developer`ToPackedArray @ out
  ]


ClebschGordanTensor[{\[Lambda]1_?NonNegativeIntegerQ, \[Lambda]2_?NonNegativeIntegerQ, \[Lambda]3_?NonNegativeIntegerQ}] :=
 ClebschGordanTensor[{\[Lambda]1, \[Lambda]2, \[Lambda]3}] =
  Module[
   {r, s, out = ConstantArray[0, {2\[Lambda]1 + 1, 2\[Lambda]2 + 1, 2\[Lambda]3 + 1}]},
   
   r = \[Lambda]1 + \[Lambda]2 - \[Lambda]3;
   s = Range[0, r];

   Do[
    out[[1 + \[Lambda]1 + m1, 1 + \[Lambda]2 + m2, 1 + \[Lambda]3 + m1 + m2]] =
     Total[
      (-1)^s * Binomial[r, s] *
      FactorialPower[\[Lambda]1 + m1, r - s] *
      FactorialPower[\[Lambda]1 - m1, s] *
      FactorialPower[\[Lambda]2 + m2, s] *
      FactorialPower[\[Lambda]2 - m2, r - s]
     ],
    {m1, -\[Lambda]1, \[Lambda]1},
    {m2, Max[-\[Lambda]2, -\[Lambda]3 - m1], Min[\[Lambda]2, \[Lambda]3 - m1]}
   ];

   Developer`ToPackedArray @ out
  ]


(* ::Subsubsection:: *)
(*EvaluateCore, BatchEvaluateCore, MultiBatchEvaluateCore, BatchMultiBatchEvaluateCore*)


(*vector*)
EvaluateCore[
 v1_,
 v2_,
 core_,
 modulus_?PrimeQ
] :=
 Mod[v2 . Mod[v1 . Mod[ClebschGordanTensor @ core, modulus], modulus], modulus]


(*batch; ...; batch; vector*)
BatchEvaluateCore[
 v1Batch_,
 v2Batch_,
 core_,
 modulus_?PrimeQ
] :=
 Mod[
  Total[
   ArrayReshape[
    v2Batch, (*this assumes that v1Batch always has at least as many axes as v2Batch, which should be the case for us*)
    Join[
     {First @ Dimensions @ v2Batch},
     ConstantArray[1, ArrayDepth @ v1Batch - ArrayDepth @ v2Batch],(*This doesn't work since Mathematica can't broadcast*)
     Rest @ Dimensions @ v2Batch
    ]
   ] * Mod[v1Batch . Mod[ClebschGordanTensor @ core, modulus], modulus],
   {ArrayDepth @ v1Batch}
  ],
  modulus
 ]


(*batch 2; batch 1; vector*)
MultiBatchEvaluateCore[
 v1MultiBatch_,
 v2MultiBatch_,
 core_,
 modulus_?PrimeQ
] :=
 Mod[
  ArrayDot[
   v2MultiBatch,
   Mod[v1MultiBatch . Mod[ClebschGordanTensor @ core, modulus], modulus],
   {{ArrayDepth @ v2MultiBatch, ArrayDepth @ v1MultiBatch}}
  ],
  modulus
 ]


(*batch; batch 2; batch 1; vector*)
BatchMultiBatchEvaluateCore[
 v1BatchMultiBatch_,
 v2BatchMultiBatch_,
 core_,
 modulus_?PrimeQ
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
 modulus_?PrimeQ,
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
 modulus_?PrimeQ,
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
 modulus_?PrimeQ,
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
 modulus_?PrimeQ,
 f_
] :=
 Mod[
  Sum[
   i[[1]] * EvaluateTensorTrain[cores, vectors, modulus, f, i[[2]]],
   {i, AntisymmetrizationData[Length @ cores + 1]}
  ],
  modulus
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
 modulus_?PrimeQ
] :=
 ConstantArray[{1}, (Dimensions @ probeBatches)[[2]]]


EvaluateYoungSymmetrizedTensorTree[
 tensorTree_Association,
 SSYT_List,
 probeBatches_List,
 modulus_?PrimeQ
] :=
 Module[
  {grids, vars, sym, antisym, final},

  (*SSYT column; CP summands; distinct variables*)
  grids = SymmetrizedMonomialCP[#, modulus] & /@ Last @ SSYT;

  (*SSYT column; distinct variables; random probe; vector*)
  vars = probeBatches[[#]] & /@ First @ SSYT;

  (*SSYT column; random probe; CP summands; vector*)
  sym = Transpose /@ MapThread[Mod[Dot[##], modulus] &, {grids, vars}];

  (*part of partition; random probe; CP summands column c; ...; CP summands column 1; vector*)
  antisym = EvaluateAntisymmetrizedTensorTrain[#, sym, modulus, BatchMultiBatchEvaluateCore] & /@ tensorTree[["leafTensorTrains"]];

  (*random probe; CP summands column c; ...; CP summands column 1; vector*)
  final = EvaluateTensorTrain[tensorTree[["interiorTensorTrain"]], antisym, modulus, BatchEvaluateCore];

  (*random probe; vector*)
  Fold[Mod[ArrayDot[#1, #2, {{2, 1}}], modulus] &, final, Reverse @ Mod[Apply[Times, grids, {2}], modulus]]
 ]


(*CP summands; multiplicity*)
SymmetrizedMonomialCP[powers_?PositiveIntegersQ, modulus_?PrimeQ] :=
 SymmetrizedMonomialCP[powers, modulus] =
  With[
   {ds = ReplacePart[powers, 1 -> 0]},
   {\[Zeta]s = PowerMod[PrimitiveRoot @ modulus, (modulus - 1) / (ds + 1), modulus]},

   Developer`ToPackedArray @ Tuples @ PowerMod[\[Zeta]s, Range[0, ds], modulus]
  ]


End[];


EndPackage[];
