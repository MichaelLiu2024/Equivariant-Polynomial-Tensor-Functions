(* ::Package:: *)

BeginPackage["ClebschGordanTools`", {"CombinatoricsTools`", "IsotypicDecompositionTools`", "TensorTools`", "BooleanTools`"}];


ClebschGordanTensor
ClebschGordanTensorTrain
TensorTrainBasisTensorProduct
TensorTrainBasisExteriorPower
TensorTrainBasisSymmetricPower
TensorTreeBasisSchurPower


Begin["`Private`"];


(* ::Subsection:: *)
(*Private Function Implementations*)


(*helper function that converts the index \[Alpha] to the corresponding spin \[Gamma]*)
indicesToPaths[
 \[Gamma]_?NonNegativeIntegerQ,
 {\[Lambda]_?NonNegativeIntegerQ, \[Alpha]_?NonNegativeIntegerQ}
] :=
 Abs[\[Gamma] - \[Lambda]] + \[Alpha] - 1


ClebschGordanTensorCache =
 File[
  "C:\\Users\\micha\\OneDrive\\Desktop\\Oden\\Notes\\Equivariant-Polynomial-Tensor-Functions-main\\Equivariant-Polynomial-Tensor-Functions-main\\ClebschGordanTensorCache.wl"
 ];


Get[ClebschGordanTensorCache]


ClebschGordanTensor[
 \[Lambda]1_?NonNegativeIntegerQ,
 \[Lambda]2_?NonNegativeIntegerQ,
 \[Lambda]3_?NonNegativeIntegerQ,
 0
] :=
ClebschGordanTensor[\[Lambda]1, \[Lambda]2, \[Lambda]3, 0] =
 Developer`ToPackedArray @ Normal @ SparseArray[
   Join @@ Table[
    {1 + \[Lambda]1 + m1, 1 + \[Lambda]2 + m2, 1 + \[Lambda]3 + m1 + m2} ->
     N @ ClebschGordan[{\[Lambda]1, m1}, {\[Lambda]2, m2}, {\[Lambda]3, m1 + m2}],
    {m1, -\[Lambda]1, \[Lambda]1},
    {m2, Max[-\[Lambda]2, -\[Lambda]3 - m1], Min[\[Lambda]2, \[Lambda]3 - m1]}
   ],
   {2 \[Lambda]1 + 1, 2 \[Lambda]2 + 1, 2 \[Lambda]3 + 1},
   0.
  ]


ClebschGordanTensor[
 \[Lambda]1_?NonNegativeIntegerQ,
 \[Lambda]2_?NonNegativeIntegerQ,
 \[Lambda]3_?NonNegativeIntegerQ,
 modulus_?PositiveIntegerQ
] :=
 ClebschGordanTensor[\[Lambda]1, \[Lambda]2, \[Lambda]3, modulus] =
  Module[
   {r, s, out},
   
   r = \[Lambda]1 + \[Lambda]2 - \[Lambda]3;
   s = Range[0, r];
   out = ConstantArray[0, {2\[Lambda]1 + 1, 2\[Lambda]2 + 1, 2\[Lambda]3 + 1}];

   Do[
    out[[1 + \[Lambda]1 + m1, 1 + \[Lambda]2 + m2, 1 + \[Lambda]3 + m1 + m2]] =
     ModReduce[modulus] @ Total[
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


ClebschGordanTensorTrain::usage = "gives the tensor train representation of the Clebsch-Gordan tensor CG(\[Lambda]s,\[Gamma]s)."


ClebschGordanTensorTrain[
 \[Lambda]s_?NonNegativeIntegersQ,
 \[Gamma]s_?NonNegativeIntegersQ,
 modulus_?NonNegativeIntegerQ
] /; Length @ \[Lambda]s == Length @ \[Gamma]s \[And] First @ \[Lambda]s == First @ \[Gamma]s \[And] If[Length @ \[Lambda]s >= 2, Abs[ListConvolve[{1, -1}, \[Gamma]s]] \[VectorLessEqual] Rest[\[Lambda]s] \[VectorLessEqual] ListConvolve[{1, 1}, \[Gamma]s], True] :=
 MapThread[ClebschGordanTensor[##, modulus] &, {Most[\[Gamma]s], Rest[\[Lambda]s], Rest[\[Gamma]s]}]


PathBasisTensorProduct::usage = "gives a list of all Clebsch-Gordan paths from \[Mu] to the tensor product of the \[Lambda]s."


PathBasisTensorProduct[
 \[Lambda]s_?NonNegativeIntegersQ,
 \[Mu]_?NonNegativeIntegerQ
] :=
 Map[
  Function[indices, FoldList[indicesToPaths, First[\[Lambda]s], Transpose[{Rest[\[Lambda]s], indices}]]],
  Position[Fold[IsotypicComponentsTensorProduct, \[Lambda]s], \[Mu]]
 ]


(* ::Subsection:: *)
(*Public Functions*)


(*basis element; tensor train*)
TensorTrainBasisTensorProduct[
 \[Lambda]s_?NonNegativeIntegersQ,
 \[Mu]_?NonNegativeIntegerQ,
 modulus_?NonNegativeIntegerQ
] :=
 ClebschGordanTensorTrain[\[Lambda]s, #, modulus] & /@ PathBasisTensorProduct[\[Lambda]s, \[Mu]]


SetAttributes[TensorTrainBasisExteriorPower, Listable]


TensorTrainBasisExteriorPower[
 \[Lambda]_?NonNegativeIntegerQ,
 d_?NonNegativeIntegerQ,
 \[Mu]_?NonNegativeIntegerQ,
 modulus_?NonNegativeIntegerQ
] /;
 d <= 3 \[And] \[Lambda] <= 3 \[And] IsotypicMultiplicityExteriorPower[\[Lambda], d, \[Mu]] > 0 :=
  Switch[
   d,
   1, {{}},
   2, {{ClebschGordanTensor[\[Lambda], \[Lambda], \[Mu], modulus]}},
   3, {ClebschGordanTensorTrain[{\[Lambda], \[Lambda], \[Lambda]}, {\[Lambda], # + 1 - Mod[#, 2] & @ Abs[\[Lambda] - \[Mu]], \[Mu]}, modulus]}
  ]


TensorTrainBasisExteriorPower[
 \[Lambda]_?NonNegativeIntegerQ,
 d_?PositiveIntegerQ,
 \[Mu]_?NonNegativeIntegerQ,
 modulus_?NonNegativeIntegerQ
] /; d > 3 \[Or] \[Lambda] > 3 :=
 Module[
  {
   interiorPaths,
   interiorTensorTrains,
   interiorRandomProbes,
   syndromeMatrix
  },

  interiorPaths =
   Select[
    PathBasisTensorProduct[ConstantArray[\[Lambda], d], \[Mu]],
    OddQ @ #[[2]] & (*ensures that the tensor is not Symmetric[{1, 2}]*)
   ];

  interiorTensorTrains = ClebschGordanTensorTrain[ConstantArray[\[Lambda], d], #, modulus] & /@ interiorPaths;

  (*part of partition; random probe; vector*)
  interiorRandomProbes =
   If[
    modulus == 0,
    RandomReal[1, {d, Ceiling[IsotypicMultiplicityExteriorPower[\[Lambda], d, \[Mu]] / (2\[Mu] + 1)] + 1, 2 \[Lambda] + 1}],
    RandomInteger[modulus - 1, {d, Ceiling[IsotypicMultiplicityExteriorPower[\[Lambda], d, \[Mu]] / (2\[Mu] + 1)] + 1, 2 \[Lambda] + 1}]
   ];

  syndromeMatrix =
   Flatten[
    EvaluateAntisymmetrizedTensorTrain[#, interiorRandomProbes, modulus, BatchEvaluateCore] & /@ interiorTensorTrains,
    {{2, 3}, {1}}
   ];

  interiorTensorTrains[[PivotColumns[syndromeMatrix, modulus]]]
 ]


TensorTrainBasisSymmetricPower::usage = "gives a list of all Clebsch-Gordan paths from \[Mu] to the d-fold symmetric power of \[Lambda]."


SetAttributes[TensorTrainBasisSymmetricPower, Listable]


TensorTrainBasisSymmetricPower[
 \[Lambda]_?NonNegativeIntegerQ,
 d_?NonNegativeIntegerQ,
 \[Mu]_?NonNegativeIntegerQ,
 modulus_?NonNegativeIntegerQ
] /;
 d <= 3 \[And] \[Lambda] <= 3 \[And] {\[Lambda], d, \[Mu]} != {3, 3, 3} \[And] IsotypicMultiplicitySymmetricPower[\[Lambda], d, \[Mu]] > 0:=
  Switch[
   d,
   1, {{}},
   2, {{ClebschGordanTensor[\[Lambda], \[Lambda], \[Mu], modulus]}},
   3, {ClebschGordanTensorTrain[{\[Lambda], \[Lambda], \[Lambda]}, {\[Lambda], # + Mod[#, 2] & @ Abs[\[Lambda] - \[Mu]], \[Mu]}, modulus]}
  ]


TensorTrainBasisSymmetricPower[
 \[Lambda]_?NonNegativeIntegerQ,
 d_?NonNegativeIntegerQ,
 \[Mu]_?NonNegativeIntegerQ,
 modulus_?NonNegativeIntegerQ
] /; d > 3 \[Or] \[Lambda] > 3 \[Or] {\[Lambda], d, \[Mu]} == {3, 3, 3} :=
 Module[
  {
  interiorPaths,
  interiorTensorTrains,
  interiorRandomProbes,
  syndromeMatrix
  },

  interiorPaths =
   Select[
    PathBasisTensorProduct[ConstantArray[\[Lambda], d], \[Mu]],
    EvenQ @ #[[2]] & (*ensures that the tensor is not Antisymmetric[{1, 2}]*)
   ];

  interiorTensorTrains = ClebschGordanTensorTrain[ConstantArray[\[Lambda], d], #, modulus] & /@ interiorPaths;

  (*random probe; vector*)
  interiorRandomProbes =
   If[
    modulus == 0,
    RandomReal[1, {Ceiling[IsotypicMultiplicitySymmetricPower[\[Lambda], d, \[Mu]] / (2\[Mu] + 1)] + 1, 2\[Lambda] + 1}],
    RandomInteger[modulus - 1, {Ceiling[IsotypicMultiplicitySymmetricPower[\[Lambda], d, \[Mu]] / (2\[Mu] + 1)] + 1, 2\[Lambda] + 1}]
   ];

  syndromeMatrix =
    Flatten[
     EvaluateSymmetrizedTensorTrain[#, interiorRandomProbes, modulus, BatchEvaluateCore] & /@ interiorTensorTrains,
     {{2, 3}, {1}}
    ];

  interiorTensorTrains[[PivotColumns[syndromeMatrix, modulus]]]
 ]


(*basis element; tensor tree*)
TensorTreeBasisSchurPower[
 \[Lambda]_?NonNegativeIntegerQ,
 {},
 \[Mu]_?NonNegativeIntegerQ,
 modulus_?NonNegativeIntegerQ
] :=
 {<|"interiorTensorTrain" -> {}, "leafTensorTrains" -> {{}}|>}


TensorTreeBasisSchurPower[
 \[Lambda]_?NonNegativeIntegerQ,
 {1},
 \[Mu]_?NonNegativeIntegerQ,
 modulus_?NonNegativeIntegerQ
] /; \[Lambda] == \[Mu] :=
 {<|"interiorTensorTrain" -> {}, "leafTensorTrains" -> {{}}|>}


TensorTreeBasisSchurPower[
 \[Lambda]_?NonNegativeIntegerQ,
 {d_?PositiveIntegerQ},
 \[Mu]_?NonNegativeIntegerQ,
 modulus_?NonNegativeIntegerQ
] /; d > 1 :=
 <|"interiorTensorTrain" -> {}, "leafTensorTrains" -> {#}|> & /@ TensorTrainBasisExteriorPower[\[Lambda], d, \[Mu], modulus]


TensorTreeBasisSchurPower[
 \[Lambda]_?NonNegativeIntegerQ,
 p_?IntegerPartitionQ,
 \[Mu]_?NonNegativeIntegerQ,
 modulus_?NonNegativeIntegerQ
] /; First @ p == 1 :=
 <|"interiorTensorTrain" -> #, "leafTensorTrains" -> ConstantArray[{}, Length @ p]|> & /@ TensorTrainBasisSymmetricPower[\[Lambda], Length @ p, \[Mu], modulus]


TensorTreeBasisSchurPower[
 \[Lambda]_?NonNegativeIntegerQ,
 p_?IntegerPartitionQ,
 \[Mu]_?NonNegativeIntegerQ,
 modulus_?NonNegativeIntegerQ
] :=
  Module[
    {
     interiorSpins,
     interiorTensorTrains,
     leafTensorTrains,
     leafRandomProbes,
     interiorRandomProbes,
     syndromeMatrix,
     linearIndices,
     interiorDimensions,
     leafDimensions,
     totalDimensions,
     tempDimensions,
     interiorSpinsIndices,
     tensorTrainIndices
    },

    (*interiorSpins*)
    interiorSpins = ConstrainedIsotypicComponentsExteriorPowers[\[Lambda], p, \[Mu]];

    (*interiorSpins; basis element; tensor train*)
    interiorTensorTrains = TensorTrainBasisTensorProduct[#, \[Mu], modulus] & /@ interiorSpins;

    (*interiorSpins; part of partition; basis element; tensor train*)
    leafTensorTrains = TensorTrainBasisExteriorPower[\[Lambda], p, #, modulus] & /@ interiorSpins;

    (*multiplicity; random probe; random vector*)
    leafRandomProbes =
     If[
      modulus == 0,
      RandomReal[1, {First @ p, Ceiling[IsotypicMultiplicitySchurPower[\[Lambda], p, \[Mu]] / (2\[Mu] + 1)] + 1, 2\[Lambda] + 1}],
      RandomInteger[modulus - 1, {First @ p, Ceiling[IsotypicMultiplicitySchurPower[\[Lambda], p, \[Mu]] / (2\[Mu] + 1)] + 1, 2\[Lambda] + 1}]
     ];

    (*interiorSpins; part of partition; basis element; random probe; syndrome vector*)
    interiorRandomProbes = Map[EvaluateAntisymmetrizedTensorTrain[#, leafRandomProbes, modulus, BatchEvaluateCore] &, leafTensorTrains, {3}];

    (*interiorSpins; part of partition; random probe; basis element; syndrome vector*)
    interiorRandomProbes = Transpose[interiorRandomProbes, 3 <-> 4];

    (*interiorSpins; basis element (interiorTensorTrains); random probe; basis elements (interiorRandomProbes); syndrome vector*)
    syndromeMatrix =
      MapThread[
       Function[
        {interiorTensorTrain, interiorRandomProbe},
        EvaluateTensorTrain[#, interiorRandomProbe, modulus, BatchMultiBatchEvaluateCore] & /@ interiorTensorTrain
       ],
       {interiorTensorTrains, interiorRandomProbes}
      ];

    (*full syndrome; interiorSpins, basis element (interiorTensorTrains), basis elements (interiorRandomProbes)*)
    syndromeMatrix =
     With[
      {maxLevel = Depth @ syndromeMatrix - 1},
      Flatten[syndromeMatrix, {{3, maxLevel}, Complement[Range @ maxLevel, {3, maxLevel}]}]
     ];

    linearIndices = PivotColumns[syndromeMatrix, modulus];

    interiorDimensions = Length /@ interiorTensorTrains;
    leafDimensions = Reverse /@ Map[Length, leafTensorTrains, {2}];
    totalDimensions = MapThread[Prepend, {leafDimensions, interiorDimensions}];
    tempDimensions = interiorDimensions * MapApply[Times, leafDimensions];

    {interiorSpinsIndices, tensorTrainIndices} =
     Transpose @ MapApply[
      {#1, ArrayMultiIndex[#2, totalDimensions[[#1]]]} &,
      RaggedMultiIndex[linearIndices, tempDimensions]
     ];

    MapThread[
     <|
      "interiorTensorTrain" -> interiorTensorTrains[[#1, First @ #2]],
      "leafTensorTrains" -> MapThread[Part, {leafTensorTrains[[#1]], Reverse @ Rest @ #2}]
     |> &,
     {interiorSpinsIndices, tensorTrainIndices}
    ]
   ]


End[];


EndPackage[];
