(* ::Package:: *)

BeginPackage["ClebschGordanTools`", {"CombinatoricsTools`", "IsotypicDecompositionTools`", "TensorTools`", "BooleanTools`"}];


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


ClebschGordanTensor::usage = "gives the elementary Clebsch-Gordan tensor coupling \[Lambda]1 and \[Lambda]2 to \[Lambda]3.";
ClebschGordanTensor[
 \[Lambda]1_?NonNegativeIntegerQ,
 \[Lambda]2_?NonNegativeIntegerQ,
 \[Lambda]3_?NonNegativeIntegerQ
] :=

ClebschGordanTensor[\[Lambda]1, \[Lambda]2, \[Lambda]3] =
Developer`ToPackedArray @ Normal @ SparseArray[
 Join @@ Table[
  {1 + \[Lambda]1 + m1, 1 + \[Lambda]2 + m2, 1 + \[Lambda]3 + m1 + m2} -> N @ ClebschGordan[{\[Lambda]1, m1}, {\[Lambda]2, m2}, {\[Lambda]3, m1 + m2}],
  {m1, -\[Lambda]1, \[Lambda]1},
  {m2, Max[-\[Lambda]2, -\[Lambda]3 - m1], Min[\[Lambda]2, \[Lambda]3 - m1]}
 ],
 {2 \[Lambda]1 + 1, 2 \[Lambda]2 + 1, 2 \[Lambda]3 + 1},
 0.
]


ValidPathQ[
 \[Lambda]s_?NonNegativeIntegersQ,
 \[Gamma]s_?NonNegativeIntegersQ
] :=

Length @ \[Lambda]s == Length @ \[Gamma]s \[And]
First @ \[Lambda]s == First @ \[Gamma]s \[And]
If[Length @ \[Lambda]s >= 2, Abs[ListConvolve[{1, -1}, \[Gamma]s]] \[VectorLessEqual] Rest[\[Lambda]s] \[VectorLessEqual] ListConvolve[{1, 1}, \[Gamma]s], True]


ClebschGordanTensorTrain::usage = "gives the tensor train representation of the Clebsch-Gordan tensor CG(\[Lambda]s,\[Gamma]s).";
ClebschGordanTensorTrain[
 \[Lambda]s_?NonNegativeIntegersQ
][
 \[Gamma]s_?NonNegativeIntegersQ
] :=

ClebschGordanTensorTrain[\[Lambda]s, \[Gamma]s]


ClebschGordanTensorTrain[
 \[Lambda]s_?NonNegativeIntegersQ,
 \[Gamma]s_?NonNegativeIntegersQ
] /;
ValidPathQ[\[Lambda]s, \[Gamma]s] :=

If[
 Length @ \[Lambda]s == 1,
 {1},
 MapThread[ClebschGordanTensor, {Most[\[Gamma]s], Rest[\[Lambda]s], Rest[\[Gamma]s]}]
]


PathBasisTensorProduct::usage = "gives a list of all Clebsch-Gordan paths from \[Mu] to the tensor product of the \[Lambda]s.";
PathBasisTensorProduct[
 \[Lambda]s_?NonNegativeIntegersQ,
 \[Mu]_?NonNegativeIntegerQ
] :=

SortBy[
 Map[
  Function[indices, FoldList[indicesToPaths, First[\[Lambda]s], Transpose[{Rest[\[Lambda]s], indices}]]],
  Position[Fold[IsotypicComponentsTensorProduct, \[Lambda]s], \[Mu]]
 ],
 FreeQ[Most @ #, 0] &
]


(* ::Subsection:: *)
(*Public Functions*)


TensorTrainBasisTensorProduct[
 \[Lambda]s_?NonNegativeIntegersQ,
 \[Mu]_?NonNegativeIntegerQ
] :=

ClebschGordanTensorTrain[\[Lambda]s] /@ PathBasisTensorProduct[\[Lambda]s, \[Mu]]


TensorTrainBasisExteriorPower::usage = "gives a list of all Clebsch-Gordan paths from \[Mu] to the d-fold exterior power of \[Lambda].";
SetAttributes[TensorTrainBasisExteriorPower, Listable]
TensorTrainBasisExteriorPower[
 \[Lambda]_?NonNegativeIntegerQ,
 d_?NonNegativeIntegerQ,
 \[Mu]_?NonNegativeIntegerQ
] /;
d <= 3 :=

Switch[
 d,
 1, {{1}},
 2, {{ClebschGordanTensor[\[Lambda], \[Lambda], \[Mu]]}},
 3, {ClebschGordanTensorTrain[{\[Lambda], \[Lambda], \[Lambda]}, {\[Lambda], # + 1 - Mod[#, 2] & @ Abs[\[Lambda] - \[Mu]], \[Mu]}]}
]


TensorTrainBasisSymmetricPower::usage = "gives a list of all Clebsch-Gordan paths from \[Mu] to the d-fold symmetric power of \[Lambda].";
SetAttributes[TensorTrainBasisSymmetricPower, Listable]
TensorTrainBasisSymmetricPower[
 \[Lambda]_?NonNegativeIntegerQ,
 d_?NonNegativeIntegerQ,
 \[Mu]_?NonNegativeIntegerQ
] /;
d <= 3 :=

Switch[
 d,
 1, {{1}},
 2, {{ClebschGordanTensor[\[Lambda], \[Lambda], \[Mu]]}},
 3, {ClebschGordanTensorTrain[{\[Lambda], \[Lambda], \[Lambda]}, {\[Lambda], # + Mod[#, 2] & @ Abs[\[Lambda] - \[Mu]], \[Mu]}]}
]


TensorTrainBasisSymmetricPower[
 \[Lambda]_?NonNegativeIntegerQ,
 d_?NonNegativeIntegerQ,
 \[Mu]_?NonNegativeIntegerQ
] /;
d >= 4 :=

Module[
 {
  interiorPaths,
  interiorTensorTrains,
  interiorRandomProbes,
  syndromeMatrix
 },
 interiorPaths = Select[PathBasisTensorProduct[ConstantArray[\[Lambda], d], \[Mu]], EvenQ @ #[[2]] &];
 interiorTensorTrains = ClebschGordanTensorTrain[ConstantArray[\[Lambda], d]] /@ interiorPaths;
 interiorRandomProbes = RandomReal[1, {Ceiling[1.1 * Length @ interiorPaths / (2 \[Mu] + 1)], 2 \[Lambda] + 1}];
 syndromeMatrix = Flatten[Outer[EvaluateSymmetrizedTensorTrain, interiorTensorTrains, interiorRandomProbes, 1], {{2, 3}, {1}}];
 interiorTensorTrains[[PivotColumns @ syndromeMatrix]]
]


TensorTreeBasisSchurPower::usage = "gives a list of all Clebsch-Gordan paths from \[Mu] to the image of the Young symmetrizer p on \[Lambda].";
TensorTreeBasisSchurPower[
 \[Lambda]_?NonNegativeIntegerQ,
 p_?IntegerPartitionQ,
 \[Mu]_?NonNegativeIntegerQ
] :=

With[
 {d = Total @ p},
 Switch[
  Length @ p,
  0, <|"interiorTensorTrains" -> {{1}}, "leafObjects" -> {{1}}|>,
  1, <|"interiorTensorTrains" -> ({1} & /@ #), "leafObjects" -> List /@ #|> & @ TensorTrainBasisExteriorPower[\[Lambda], d, \[Mu]],
  d, <|"interiorTensorTrains" -> #, "leafObjects" -> (ConstantArray[{1}, d] & /@ #)|> & @ TensorTrainBasisSymmetricPower[\[Lambda], d, \[Mu]],
  _,
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
   interiorSpins = SortBy[ConstrainedIsotypicComponentsExteriorPowers[\[Lambda], p, \[Mu]], FreeQ[#, 0] &];
   interiorTensorTrains = TensorTrainBasisTensorProduct[#, \[Mu]] & /@ interiorSpins;
   leafTensorTrains = TensorTrainBasisExteriorPower[\[Lambda], p, #] & /@ interiorSpins;
   interiorDimensions = Length /@ interiorTensorTrains;
   leafDimensions = Map[Length, leafTensorTrains, {2}];
   totalDimensions = MapThread[Prepend, {leafDimensions, interiorDimensions}];
   tempDimensions = interiorDimensions * MapApply[Times, leafDimensions];
   leafRandomProbes = RandomReal[1, {Ceiling[1.1 * Total[tempDimensions] / (2 \[Mu] + 1)], First @ p, 2 \[Lambda] + 1}];
   interiorRandomProbes = Outer[EvaluateAntisymmetrizedTensorTrain, leafTensorTrains, leafRandomProbes, 3, 1];
   interiorRandomProbes = Transpose[interiorRandomProbes, {1, 3, 4, 2}];
   syndromeMatrix = MapThread[Function[{interiorTensorTrain, interiorRandomProbe}, Outer[EvaluateTensorTrain, interiorTensorTrain, Tuples /@ interiorRandomProbe, 1, 2]], {interiorTensorTrains, interiorRandomProbes}];
   syndromeMatrix = Flatten[syndromeMatrix, {{3, 5}, {1, 2, 4}}];
   linearIndices = PivotColumns @ syndromeMatrix;
   {interiorSpinsIndices, tensorTrainIndices} = Transpose @ MapApply[{#1, ArrayMultiIndex[#2, totalDimensions[[#1]]]} &, RaggedMultiIndex[linearIndices, tempDimensions]];
   <|
   "interiorTensorTrains" -> MapThread[interiorTensorTrains[[#1, First @ #2]] &, {interiorSpinsIndices, tensorTrainIndices}],
   "leafObjects" -> MapThread[MapThread[Part, {leafTensorTrains[[#1]], Rest @ #2}] &, {interiorSpinsIndices, tensorTrainIndices}]
   |>
  ]
 ]
]


End[];


EndPackage[];
