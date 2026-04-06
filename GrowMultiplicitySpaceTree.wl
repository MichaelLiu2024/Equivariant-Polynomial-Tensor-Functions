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


EvaluateBasis


Begin["`Private`"];


(* ::Subsubsection:: *)
(*Public Functions*)


IsotypicDataTree[
 \[Lambda]s_?DistinctPositiveIntegersQ,
 m\[Lambda]s_?PositiveIntegersQ,
 \[Nu]_?NonNegativeIntegerQ,
 DMax_?NonNegativeIntegerQ
] /; Length @ \[Lambda]s == Length @ m\[Lambda]s :=
 Module[
  {tree},

  (*D*)
  tree = Tree[{\[Lambda]s, m\[Lambda]s, \[Nu], DMax}, Range[0, DMax]];

  (*d\[Lambda]s*)
  tree = NestTree[WeakCompositions[#, Length[\[Lambda]s]] &, tree];

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
  AncestralNestTree[TensorProductBasis, tree]
 ]


VectorSpaceBasis[IsotypicDataTree_Tree] :=
 Lookup[
  Association[
   TreeData @ # -> TreeData /@ TreeLeaves @ # & /@ TreeChildren @ IsotypicDataTree
  ],
  Range[0, Last @ TreeData @ IsotypicDataTree],
  {}
 ]


AlgebraBasis[invariantIsotypicDataTree_Tree] :=
 Module[
  {
   \[Lambda]s, m\[Lambda]s, \[Nu], DMax,
   vectorSpaceBasis,
   randomProbes,
   invariantSyndromes,
   productSyndromes,
   linearIndices
  },
  
  {\[Lambda]s, m\[Lambda]s, \[Nu], DMax} = TreeData @ invariantIsotypicDataTree;
  
  vectorSpaceBasis = VectorSpaceBasis @ invariantIsotypicDataTree;

  (*\[Lambda]; random probe; multiplicity; random vector*)
  randomProbes =
   generateRandomProbes[
    \[Lambda]s,
    m\[Lambda]s,
    Max @ spaceDimensions @ vectorSpaceBasis
   ];

  (*degree; leaf; random probe; interiorTensorTrains; SSYTs, tensorTrees for each \[Lambda]; output vector*)
  invariantSyndromes = EvaluateBasis[vectorSpaceBasis, randomProbes];

  (*degree; random probe; leaf, interiorTensorTrains, SSYTs, tensorTrees for each \[Lambda]; output vector*)
  invariantSyndromes = Flatten[invariantSyndromes, flattenLevels[Length @ \[Lambda]s]];


  (*NEW CODE SHOULD START HERE*)


  (*degree; random probe; columns*)
  productSyndromes =
   Table[
    RowJoin @@
     Table[
      RowKroneckerProduct[invariantSyndromes[[i]], invariantSyndromes[[d + 1 - i]]],
      {i, Ceiling[d / 2], 1, -1}
     ],
    {d, 1, DMax + 1}
   ];

  (*degree; indices into productSyndromes*)
  linearIndices = PivotColumns /@ productSyndromes;

  (*degree; indices into invariantSyndromes*)
  linearIndices =
   MapThread[
    DeleteCases[#1, i_ /; i <= #2] - #2 &,
    {
     linearIndices,
     Last @* Dimensions /@ productSyndromes -
      Last @* Most @* Dimensions /@ invariantSyndromes
    }
   ];

  extract[linearIndices, vectorSpaceBasis]
 ]


ModuleBasis[
 invariantIsotypicDataTree_Tree,
 covariantIsotypicDataTree_Tree
] :=
 Module[
  {
   \[Lambda]s, m\[Lambda]s, \[Nu], DMax,
   invariantVectorSpaceBasis,
   covariantVectorSpaceBasis,
   randomProbes,
   levels,
   invariantSyndromes,
   covariantSyndromes,
   productSyndromes,
   linearIndices
  },

  {\[Lambda]s, m\[Lambda]s, \[Nu], DMax} = TreeData @ covariantIsotypicDataTree;

  invariantVectorSpaceBasis = VectorSpaceBasis @ invariantIsotypicDataTree;
  
  covariantVectorSpaceBasis = VectorSpaceBasis @ covariantIsotypicDataTree;

  randomProbes =
   generateRandomProbes[
    \[Lambda]s,
    m\[Lambda]s,
    Ceiling[Max @ spaceDimensions @ covariantVectorSpaceBasis / (2 \[Nu] + 1)]
   ];

  levels = flattenLevels[Length @ \[Lambda]s];

  invariantSyndromes = EvaluateBasis[invariantVectorSpaceBasis, randomProbes];
  invariantSyndromes = Flatten[invariantSyndromes, levels];

  covariantSyndromes = EvaluateBasis[covariantVectorSpaceBasis, randomProbes];
  covariantSyndromes = Flatten[covariantSyndromes, levels];

  productSyndromes =
   ListConvolve[
    invariantSyndromes,
    covariantSyndromes,
    1,
    {{{{}}}},
    RowKroneckerProduct,
    RowJoin
   ];

  linearIndices = PivotColumns /@ productSyndromes;

  (*indices into covariantSyndromes*)
  linearIndices =
   MapThread[
    DeleteCases[#1, i_ /; i <= #2] - #2 &,
    {
     linearIndices,
     Last @* Dimensions /@ productSyndromes -
      Last @* Most @* Dimensions /@ covariantSyndromes
    }
   ];

  extract[linearIndices, covariantVectorSpaceBasis]
 ]


EvaluateBasis[
 VectorSpaceBasis_List,
 inputVectors_List
] :=
 Map[
  EvaluateTensorProductBasis[#, inputVectors] &,
  VectorSpaceBasis,
  {2}
 ]


(* ::Subsubsection:: *)
(*Private Functions*)


generateRandomProbes[
 \[Lambda]s_?DistinctPositiveIntegersQ,
 m\[Lambda]s_?PositiveIntegersQ,
 numProbes_Integer
] /; Length @ \[Lambda]s == Length @ m\[Lambda]s :=
 MapThread[
  Function[{\[Lambda], m\[Lambda]}, RandomReal[1, {numProbes, m\[Lambda], 2 \[Lambda] + 1}]],
  {\[Lambda]s, m\[Lambda]s}
 ]


flattenLevels[n_?PositiveIntegerQ] :=
 With[
  {maxLvl = 5 + 2 * n},
  {{1}, {3}, Complement[Range @ maxLvl, {1, 3, maxLvl}], {maxLvl}}
 ]


extract[
 linearIndices_List,
 basis_List
] :=
 Module[
  {leafIndices, finalIndices, fullDimensions, leafDimensions},

  fullDimensions =
   Map[#[["dimensions"]] &, basis, {2}];
  (*degree; leaf; list of dimensions: interiorTensorTrains; SSYTs,tensorTrees for each \[Lambda]*)

  leafDimensions = Apply[Times, fullDimensions, {2}];

  leafIndices =
   MapThread[
    RaggedMultiIndex,
    {linearIndices, leafDimensions}
   ];
  (*degree; linearIndices; {index into leaf, linear index into interiorTensorTrains; SSYTs,tensorTrees for each \[Lambda]}*)

  finalIndices =
   MapThread[
    Function[{lIndices, dims}, MapApply[{#1, ArrayMultiIndex[#2, dims[[#1]]]} &, lIndices]],
    {leafIndices, fullDimensions}
   ];
  (*degree; linearIndices; {index into leaf, multiindex into interiorTensorTrains; SSYTs,tensorTrees for each \[Lambda]}*)

  MapThread[
   Function[
    {indices, TensorProductBases},
    MapApply[
     <|
       "interiorTensorTrains" ->
        {TensorProductBases[[#1]][["interiorTensorTrains"]][[First @ #2]]},
       "SSYT\[Lambda]s" ->
        MapThread[
         List @* Part,
         {TensorProductBases[[#1]][["SSYT\[Lambda]s"]], Rest[#2][[1 ;; ;; 2]]}
        ],
       "leafObjects" ->
        MapThread[
         Function[
          {assoc, index},
          <|
            "interiorTensorTrains" -> {assoc[["interiorTensorTrains"]][[index]]},
            "leafObjects" -> {assoc[["leafObjects"]][[index]]}
          |>
         ],
         {TensorProductBases[[#1]][["leafObjects"]], Rest[#2][[2 ;; ;; 2]]}
        ]
      |> &,
     indices
    ]
   ],
   {finalIndices, basis}
  ]
 ]


TensorProductBasis[
 {
  {\[Lambda]s_, m\[Lambda]s_, \[Nu]_},
  D_,
  d\[Lambda]s_,
  \[Pi]\[Lambda]s_,
  \[Mu]\[Lambda]s_
 }
] :=
 With[
  {
   interiorTensorTrains = TensorTrainBasisTensorProduct[\[Mu]\[Lambda]s, \[Nu]],
   leafObjects = MapThread[TensorTreeBasisSchurPower, {\[Lambda]s, \[Pi]\[Lambda]s, \[Mu]\[Lambda]s}],
   SSYT\[Lambda]s = MapThread[SemiStandardYoungTableaux, {\[Pi]\[Lambda]s, m\[Lambda]s}]
  },
  {
   <|
    "interiorTensorTrains" -> interiorTensorTrains,
    "leafObjects" -> leafObjects,
    "SSYT\[Lambda]s" -> SSYT\[Lambda]s,
    "dimensions" ->
     Flatten[
      {
       Length @ interiorTensorTrains,
       Transpose[
        {
         Length /@ SSYT\[Lambda]s,
         Length @ #[["leafObjects"]] & /@ leafObjects
        }
       ]
      }
     ]
   |>
  }
 ]


EvaluateTensorProductBasis[
 basis_Association,
 inputVectors_List
] :=
 Module[
  {interiorVectors, outputVectors},

  (*inputVectors; \[Lambda]; SSYTs; tensorTrees; interiorVectors*)
  interiorVectors =
   Transpose @
    MapThread[
     EvaluateYoungSymmetrizedTensorTree,
     {basis[["leafObjects"]], basis[["SSYT\[Lambda]s"]], inputVectors}
    ];

  (*inputVectors; interiorTensorTrains; SSYTs, tensorTrees for each \[Lambda]; outputVectors*)
  outputVectors =
   Outer[
     EvaluateTensorTrain[#1, {##2}] &,
     basis[["interiorTensorTrains"]],
     Sequence @@ #,
     1,
     Sequence @@ ConstantArray[2, Length @ inputVectors]
   ] & /@ interiorVectors
 ]

End[];

EndPackage[];
