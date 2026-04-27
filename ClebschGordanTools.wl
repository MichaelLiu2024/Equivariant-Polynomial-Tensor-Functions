(* ::Package:: *)

BeginPackage["ClebschGordanTools`", {"CombinatoricsTools`", "IsotypicDecompositionTools`", "TensorTools`", "BooleanTools`"}];


TensorTrainBasisTensorProduct
TensorTrainBasisExteriorPower
TensorTrainBasisSymmetricPower
TensorTreeBasisSchurPower


Begin["`Private`"];


(* ::Subsubsection:: *)
(*TensorTrainBasisTensorProduct*)


(*helper function that converts the index \[Alpha] to the corresponding spin \[Gamma]*)
indicesToPaths[
 \[Gamma]_?NonNegativeIntegerQ,
 {\[Lambda]_?NonNegativeIntegerQ, \[Alpha]_?NonNegativeIntegerQ}
] :=
 Abs[\[Gamma] - \[Lambda]] + \[Alpha] - 1


(*basis element; tensor train*)
TensorTrainBasisTensorProduct[
 \[Lambda]s_?NonNegativeIntegersQ,
 \[Mu]_?NonNegativeIntegerQ
] :=
 With[
  {
   all\[Gamma]s =
    Map[
     Function[indices, FoldList[indicesToPaths, First[\[Lambda]s], Transpose[{Rest[\[Lambda]s], indices}]]],
     Position[Fold[IsotypicComponentsTensorProduct, \[Lambda]s], \[Mu]]
    ]
  },
  
  Transpose @ {Most @ #, Rest @ \[Lambda]s, Rest @ #} & /@ all\[Gamma]s
 ]


(* ::Subsubsection:: *)
(*TensorTrainBasisExteriorPower*)


SetAttributes[TensorTrainBasisExteriorPower, Listable]


TensorTrainBasisExteriorPower[
 \[Lambda]_?NonNegativeIntegerQ,
 d_?NonNegativeIntegerQ,
 \[Mu]_?NonNegativeIntegerQ
] /; d <= 3 \[And] \[Lambda] <= 3 \[And] IsotypicMultiplicityExteriorPower[\[Lambda], d, \[Mu]] > 0 :=
 Switch[
  d,
  1, {{}},
  2, {{{\[Lambda], \[Lambda], \[Mu]}}},
  3, With[{\[Gamma] = BitOr[Abs[\[Lambda] - \[Mu]], 1] (*\[Gamma] is the smallest odd integer >= Abs[\[Lambda] - \[Mu]]*)}, {{{\[Lambda], \[Lambda], \[Gamma]}, {\[Gamma], \[Lambda], \[Mu]}}}]
 ]


TensorTrainBasisExteriorPower[
 \[Lambda]_?NonNegativeIntegerQ,
 d_?PositiveIntegerQ,
 \[Mu]_?NonNegativeIntegerQ
] /; (d > 3 \[Or] \[Lambda] > 3) \[And] IsotypicMultiplicityExteriorPower[\[Lambda], d, \[Mu]] > 0 :=
 Module[
  {
   dim = IsotypicMultiplicityExteriorPower[\[Lambda], d, \[Mu]],
   modulus,
   interiorTensorTrains,
   interiorRandomProbes,
   syndromeMatrix
  },
  
  modulus = NextPrime[\[Lambda] dim d];

  interiorTensorTrains =
   Select[
    TensorTrainBasisTensorProduct[ConstantArray[\[Lambda], d], \[Mu]],
    OddQ @ #[[1, 3]] & (*ensures that the tensor is not Symmetric[{1, 2}]*)
   ];

  (*part of partition; random probe; vector*)
  interiorRandomProbes = RandomInteger[modulus - 1, {d, Ceiling[dim / (2\[Mu] + 1)] + 1, 2 \[Lambda] + 1}];

  syndromeMatrix =
   Flatten[
    EvaluateAntisymmetrizedTensorTrain[#, interiorRandomProbes, modulus, BatchEvaluateCore] & /@ interiorTensorTrains,
    {{2, 3}, {1}}
   ];

  interiorTensorTrains[[PivotColumns[syndromeMatrix, modulus]]]
 ]


(* ::Subsubsection:: *)
(*TensorTrainBasisSymmetricPower*)


SetAttributes[TensorTrainBasisSymmetricPower, Listable]


TensorTrainBasisSymmetricPower[
 \[Lambda]_?NonNegativeIntegerQ,
 d_?NonNegativeIntegerQ,
 \[Mu]_?NonNegativeIntegerQ
] /; d <= 3 \[And] \[Lambda] <= 3 \[And] {\[Lambda], d, \[Mu]} != {3, 3, 3} \[And] IsotypicMultiplicitySymmetricPower[\[Lambda], d, \[Mu]] > 0 :=
 Switch[
  d,
  1, {{}},
  2, {{{\[Lambda], \[Lambda], \[Mu]}}},
  3, With[{\[Gamma] = BitAnd[Abs[\[Lambda] - \[Mu]] + 1, -2] (*\[Gamma] is the smallest even integer >= Abs[\[Lambda] - \[Mu]]*)}, {{{\[Lambda], \[Lambda], \[Gamma]}, {\[Gamma], \[Lambda], \[Mu]}}}]
 ]


TensorTrainBasisSymmetricPower[
 \[Lambda]_?NonNegativeIntegerQ,
 d_?NonNegativeIntegerQ,
 \[Mu]_?NonNegativeIntegerQ
] /; (d > 3 \[Or] \[Lambda] > 3 \[Or] {\[Lambda], d, \[Mu]} == {3, 3, 3}) \[And] IsotypicMultiplicitySymmetricPower[\[Lambda], d, \[Mu]] > 0 :=
 Module[
  {
   dim = IsotypicMultiplicitySymmetricPower[\[Lambda], d, \[Mu]],
   modulus,
   interiorTensorTrains,
   interiorRandomProbes,
   syndromeMatrix
  },
  
  modulus = NextPrime[\[Lambda] dim d];
  
  interiorTensorTrains =
   Select[
    TensorTrainBasisTensorProduct[ConstantArray[\[Lambda], d], \[Mu]],
    EvenQ @ #[[1, 3]] & (*ensures that the tensor is not Antisymmetric[{1, 2}]*)
   ];

  (*random probe; vector*)
  interiorRandomProbes = RandomInteger[modulus - 1, {Ceiling[dim / (2\[Mu] + 1)] + 1, 2\[Lambda] + 1}];

  syndromeMatrix =
    Flatten[
     EvaluateSymmetrizedTensorTrain[#, interiorRandomProbes, modulus, BatchEvaluateCore] & /@ interiorTensorTrains,
     {{2, 3}, {1}}
    ];

  interiorTensorTrains[[PivotColumns[syndromeMatrix, modulus]]]
 ]


(* ::Subsubsection:: *)
(*TensorTreeBasisSchurPower*)


(*basis element; tensor tree*)
TensorTreeBasisSchurPower[
 \[Lambda]_?NonNegativeIntegerQ,
 {},
 \[Mu]_?NonNegativeIntegerQ
] :=
 {<|"interiorTensorTrain" -> {}, "leafTensorTrains" -> {{}}|>}


TensorTreeBasisSchurPower[
 \[Lambda]_?NonNegativeIntegerQ,
 {1},
 \[Mu]_?NonNegativeIntegerQ
] /; \[Lambda] == \[Mu] :=
 {<|"interiorTensorTrain" -> {}, "leafTensorTrains" -> {{}}|>}


TensorTreeBasisSchurPower[
 \[Lambda]_?NonNegativeIntegerQ,
 {d_?PositiveIntegerQ},
 \[Mu]_?NonNegativeIntegerQ
] /; d > 1 :=
 <|"interiorTensorTrain" -> {}, "leafTensorTrains" -> {#}|> & /@ TensorTrainBasisExteriorPower[\[Lambda], d, \[Mu]]


TensorTreeBasisSchurPower[
 \[Lambda]_?NonNegativeIntegerQ,
 p_?IntegerPartitionQ,
 \[Mu]_?NonNegativeIntegerQ
] /; First @ p == 1 :=
 <|"interiorTensorTrain" -> #, "leafTensorTrains" -> ConstantArray[{}, Length @ p]|> & /@ TensorTrainBasisSymmetricPower[\[Lambda], Length @ p, \[Mu]]


TensorTreeBasisSchurPower[
 \[Lambda]_?NonNegativeIntegerQ,
 p_?IntegerPartitionQ,
 \[Mu]_?NonNegativeIntegerQ
] :=
  Module[
    {
     dim = IsotypicMultiplicitySchurPower[\[Lambda], p, \[Mu]],
     modulus,
     
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

    modulus = NextPrime[\[Lambda] dim Total @ p];
    
    (*interiorSpins*)
    interiorSpins = ConstrainedIsotypicComponentsExteriorPowers[\[Lambda], p, \[Mu]];

    (*interiorSpins; basis element; tensor train*)
    interiorTensorTrains = TensorTrainBasisTensorProduct[#, \[Mu]] & /@ interiorSpins;

    (*interiorSpins; part of partition; basis element; tensor train*)
    leafTensorTrains = TensorTrainBasisExteriorPower[\[Lambda], p, #] & /@ interiorSpins;

    (*multiplicity; random probe; random vector*)
    leafRandomProbes = RandomInteger[modulus - 1, {First @ p, Ceiling[dim / (2\[Mu] + 1)] + 1, 2\[Lambda] + 1}];

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
