(* ::Package:: *)

BeginPackage[
 "GrowMultiplicitySpaceTree`",
 {
  "TreeTools`",
  "TensorTools`",
  "ClebschGordanTools`",
  "IsotypicDecompositionTools`",
  "CombinatoricsTools`",
  "BooleanTools`"
 }
];


IsotypicDataTree


VectorSpaceBasis


AlgebraBasis


ModuleBasis


Begin["`Private`"];


(* ::Subsubsection:: *)
(*Public Functions*)


IsotypicDataTree[
 \[Lambda]s_?DistinctPositiveIntegersQ,
 m\[Lambda]s_?PositiveIntegersQ,
 \[Nu]_?NonNegativeIntegerQ,
 DMax_?NonNegativeIntegerQ,
 modulus_?NonNegativeIntegerQ
] /; Length @ \[Lambda]s == Length @ m\[Lambda]s :=
 Module[
  {tree},

  (*D*)
  tree = Tree[{\[Lambda]s, m\[Lambda]s, \[Nu], DMax, modulus}, Range @ DMax];

  (*d\[Lambda]s*)
  tree = NestTree[WeakCompositions[#, Length @ \[Lambda]s] &, tree];

  (*\[Pi]\[Lambda]s*)
  tree = NestTree[Tuples @ ThinPartitions[#, \[Lambda]s, m\[Lambda]s] &, tree];

  (*\[Mu]\[Lambda]s*)
  tree =
   PruneChildlessNodes @
    NestTree[
     ConstrainedIsotypicComponentsSchurPowers[\[Lambda]s, #, \[Nu]] &,
     tree
    ];

  (*TensorProductBasis*)
  AncestralNestTree[List @* TensorProductBasis, tree]
 ]


TensorProductBasis[
 {
  {\[Lambda]s_, m\[Lambda]s_, \[Nu]_, DMax_, modulus_},
  D_,
  d\[Lambda]s_,
  \[Pi]\[Lambda]s_,
  \[Mu]\[Lambda]s_
 }
] :=
 <|
  "interiorTensorTrains" -> TensorTrainBasisTensorProduct[\[Mu]\[Lambda]s, \[Nu], modulus],
  "leafTensorTrees" -> MapThread[TensorTreeBasisSchurPower[##, modulus] &, {\[Lambda]s, \[Pi]\[Lambda]s, \[Mu]\[Lambda]s}],
  "SSYT\[Lambda]s" -> MapThread[SemiStandardYoungTableaux, {\[Pi]\[Lambda]s, m\[Lambda]s}]
 |>


VectorSpaceBasis[IsotypicDataTree_Tree] :=
 Lookup[
  Association[
   TreeData @ # -> TreeData /@ TreeLeaves @ # & /@ TreeChildren @ IsotypicDataTree
  ],
  Range[(TreeData @ IsotypicDataTree)[[4]]],
  {}
 ]


extractIndependentGenerators[
 invariantIsotypicDataTree_Tree,
 covariantIsotypicDataTree_Tree,
 probeTarget_,
 degreeLimit_
] :=
 Module[
  {
   \[Lambda]s, m\[Lambda]s, \[Nu], DMax, modulus,
   invariantVectorSpaceBasis,
   covariantVectorSpaceBasis,
   targetNumProbes,
   probeBatches\[Lambda]s,
   invariantSyndromes,
   covariantGenerators,
   covariantSyndromes,
   candidateSyndromes,
   previousProductSyndromes,
   numPreviousColumns,
   linearIndices,
   degree,
   i
  },

  {\[Lambda]s, m\[Lambda]s, \[Nu], DMax, modulus} = TreeData @ covariantIsotypicDataTree;

  invariantVectorSpaceBasis = VectorSpaceBasis @ invariantIsotypicDataTree;

  covariantVectorSpaceBasis = VectorSpaceBasis @ covariantIsotypicDataTree;

  targetNumProbes = probeTarget[HilbertSeries[\[Lambda]s, m\[Lambda]s, \[Nu], DMax], \[Nu]];

  probeBatches\[Lambda]s =
   MapThread[
    If[
     modulus == 0,
     Function[{\[Lambda], m\[Lambda]}, RandomReal[1, {m\[Lambda], Max @ targetNumProbes, 2 \[Lambda] + 1}]],
     Function[{\[Lambda], m\[Lambda]}, RandomInteger[modulus - 1, {m\[Lambda], Max @ targetNumProbes, 2 \[Lambda] + 1}]]
    ],
    {\[Lambda]s, m\[Lambda]s}
   ];

  covariantGenerators = ConstantArray[{}, DMax];

  covariantSyndromes = ConstantArray[{}, DMax];

  invariantSyndromes = computeSyndromes[invariantVectorSpaceBasis[[#]], probeBatches\[Lambda]s, modulus] & /@ Range @ DMax;

  covariantGenerators[[1]] = covariantVectorSpaceBasis[[1]];

  covariantSyndromes[[1]] = computeSyndromes[covariantGenerators[[1]], probeBatches\[Lambda]s, modulus];

  For[
   degree = 2, degree <= DMax, degree++,

   (*If there are no vector space generators at the current degree, then there are no covariant generators at the current degree*)
   If[covariantVectorSpaceBasis[[degree]] === {}, Continue[]];

   (*Compute previous product syndromes*)
   previousProductSyndromes =
    Table[
     If[
      invariantSyndromes[[degree - i]] =!= {} \[And] covariantSyndromes[[i]] =!= {},
      ModReduce[modulus] @ RowKroneckerProduct[
       invariantSyndromes[[degree - i, ;; targetNumProbes[[degree]]]],
       covariantSyndromes[[i, ;; targetNumProbes[[degree]]]]
      ],
      Nothing
     ],
     {i, 1, degreeLimit[degree]}
    ];

   (*Compute new syndromes*)
   candidateSyndromes = computeSyndromes[covariantVectorSpaceBasis[[degree]], probeBatches\[Lambda]s[[All, All, ;; targetNumProbes[[degree]]]], modulus];

   numPreviousColumns = Total[(Dimensions @ #)[[2]] & /@ previousProductSyndromes];

   linearIndices =
    DeleteCases[
     PivotColumns[Flatten[Append[previousProductSyndromes, candidateSyndromes], {{2, 4}, {1, 3}}], modulus],
     j_ /; j <= numPreviousColumns
    ] - numPreviousColumns;

   covariantGenerators[[degree]] = extract[linearIndices, covariantVectorSpaceBasis[[degree]]];

   If[
    degree < DMax,

    covariantSyndromes[[degree]] = candidateSyndromes[[All, linearIndices]];

    If[
     targetNumProbes[[degree]] < Max @ targetNumProbes,

     covariantSyndromes[[degree]] =
      Join[
       covariantSyndromes[[degree]],
       computeSyndromes[covariantGenerators[[degree]], probeBatches\[Lambda]s[[All, All, targetNumProbes[[degree]] + 1 ;;]], modulus]
      ]
    ]
   ]
  ];

  covariantGenerators
 ]


AlgebraBasis[invariantIsotypicDataTree_Tree] :=
 extractIndependentGenerators[
  invariantIsotypicDataTree,
  invariantIsotypicDataTree,
  Function[{dimensions, \[Nu]}, dimensions],
  Function[degree, Floor[degree / 2]]
 ]


ModuleBasis[
 invariantIsotypicDataTree_Tree,
 covariantIsotypicDataTree_Tree
] :=
 extractIndependentGenerators[
  invariantIsotypicDataTree,
  covariantIsotypicDataTree,
  Function[{dimensions, \[Nu]}, Ceiling[dimensions / (2 \[Nu] + 1)]],
  Function[degree, degree - 1]
 ]


(* ::Subsubsection:: *)
(*Private Functions*)


computeSyndromes[
 {},
 probeBatches\[Lambda]s_List,
 modulus_?NonNegativeIntegerQ
] :=
 {}


(*random probe; leaf, indices; vector*)
computeSyndromes[
 polynomials_List,
 probeBatches\[Lambda]s_List,
 modulus_?NonNegativeIntegerQ
] :=
 Flatten[EvaluateTensorProductBasis[#, probeBatches\[Lambda]s, modulus] & /@ polynomials, {{2}, {1, 3}, {4}}]


extract[
 linearIndices_List,
 basis_List
] :=
 Module[
  {leafIndices, finalIndices, fullDimensions, leafDimensions},

  (*leaf; {dim interiorTensorTrains, (tensorTrees; SSYTs; for the last \[Lambda]) ... (tensorTrees; SSYTs; for the first \[Lambda])}*)
  fullDimensions = tpDimensions /@ basis;

  (*leaf; product of dimensions*)
  leafDimensions = MapApply[Times, fullDimensions];

  (*linearIndices; {index into leaf, linear index into (tensorTrees; SSYTs; for the last \[Lambda]) ... (tensorTrees; SSYTs; for the first \[Lambda])}*)
  leafIndices = RaggedMultiIndex[linearIndices, leafDimensions];

  (*linearIndices; {index into leaf, multiindex into interiorTensorTrains, (tensorTrees; SSYTs; for the last \[Lambda]) ... (tensorTrees; SSYTs; for the first \[Lambda])}*)
  finalIndices = MapApply[{#1, ArrayMultiIndex[#2, fullDimensions[[#1]]]} &, leafIndices];

  MapApply[
   <|
    "interiorTensorTrains" -> {basis[[#1]][["interiorTensorTrains"]][[First @ #2]]},
    "SSYT\[Lambda]s" ->
     MapThread[
      List @* Part,
      {basis[[#1]][["SSYT\[Lambda]s"]], (Reverse @ Rest @ #2)[[1 ;; ;; 2]]}
     ],
    "leafTensorTrees" ->
     MapThread[
      Function[
       {tensorTree, index},
       {
        <|
         "interiorTensorTrain" -> tensorTree[[index]][["interiorTensorTrain"]],
         "leafTensorTrains" -> tensorTree[[index]][["leafTensorTrains"]]
        |>
       }
      ],
      {basis[[#1]][["leafTensorTrees"]], (Reverse @ Rest @ #2)[[2 ;; ;; 2]]}
     ]
   |> &,
   finalIndices
  ]
 ]


EvaluateTensorProductBasis[
 basis_Association,
 probeBatches\[Lambda]s_List,
 modulus_?NonNegativeIntegerQ
] :=
 Module[
  {interiorVectors, outputVectors, maxLevel},

  (*\[Lambda]; tensorTrees; SSYTs; random probe; vector*)
  interiorVectors =
   MapThread[
    Function[{tensorTrees, SSYTs, probeBatches}, Outer[EvaluateYoungSymmetrizedTensorTree[#1, #2, probeBatches, modulus] &, tensorTrees, SSYTs, 1]],
    {basis[["leafTensorTrees"]], basis[["SSYT\[Lambda]s"]], probeBatches\[Lambda]s}
   ];

  (*\[Lambda]; random probe; tensorTrees; SSYTs; vector*)
  interiorVectors = Flatten[interiorVectors, {{1}, {4}, {2}, {3}, {5}}];

  (*interiorTensorTrains; randomProbes; (tensorTrees; SSYTs; for the last \[Lambda]) ... (tensorTrees; SSYTs; for the first \[Lambda]); vector*)
  outputVectors = EvaluateTensorTrain[#, interiorVectors, modulus, BatchMultiBatchEvaluateCore] & /@ basis[["interiorTensorTrains"]];

  maxLevel = 3 + 2 * Length @ basis[["SSYT\[Lambda]s"]];

  (*randomProbes; interiorTensorTrains, (tensorTrees, SSYTs, for the last \[Lambda]) ... (tensorTrees, SSYTs, for the first \[Lambda]); vector*)
  Flatten[outputVectors,{{2}, Complement[Range @ maxLevel, {2, maxLevel}], {maxLevel}}]
 ]


End[];

EndPackage[];
