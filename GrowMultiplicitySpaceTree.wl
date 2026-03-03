(* ::Package:: *)

BeginPackage["GrowMultiplicitySpaceTree`",{"TreeTools`","TensorTools`","ClebschGordanTools`","IsotypicDecompositionTools`","CombinatoricsTools`","BooleanTools`"}];


IsotypicDataTree
VectorSpaceBasis
AlgebraBasis
ModuleBasis
EvaluateBasis


Begin["`Private`"];


(* ::Subsubsection:: *)
(*Private Functions*)


RowKroneckerProduct[
 m1_List?ArrayQ,
 {{{}}}
] :=
{{}}
RowKroneckerProduct[
 {{{}}},
 m2_List?ArrayQ
] :=
{{}}
RowKroneckerProduct[
 m1_List?ArrayQ,
 m2_List?ArrayQ
] /;
 Length@m1==Length@m2\[And]Depth@m1==4==Depth@m2 :=

  Flatten[
   MapThread[KroneckerProduct,{m1,m2}],
   {{1,3},{2}}
  ]


RowJoin[
 ms__
] :=
Join[ms,2]


generateRandomProbes[
 \[Lambda]s_?DistinctPositiveIntegersQ,
 m\[Lambda]s_?PositiveIntegersQ,
 numProbes_Integer
] /;
 Length@\[Lambda]s==Length@m\[Lambda]s :=

  MapThread[
   Function[{\[Lambda],m\[Lambda]},RandomReal[1,{numProbes,m\[Lambda],2\[Lambda]+1}]],
   {\[Lambda]s,m\[Lambda]s}
  ]


flattenLevels[
 n_?PositiveIntegerQ
] :=

 With[
  {maxLvl=5+2*n},
  {{1},{3},Complement[Range@maxLvl,{1,3,maxLvl}],{maxLvl}}
 ];


dims[
 VectorSpaceBasis_List
] :=
Total/@Map[Times@@#[["dimensions"]]&,VectorSpaceBasis,{2}]


algebraDimensionBound[
 invariantBasis_List
] :=

 With[
  {invariantDims=dims[invariantBasis]},
  
  Ceiling[
   1.1*Max@Table[
    Sum[
     invariantDims[[i]]*invariantDims[[d+1-i]],
     {i,Ceiling[d/2],1,-1}
    ],
    {d,1,Length@invariantBasis}
   ]
  ]
 ]


moduleDimensionBound[
 \[Nu]_?NonNegativeIntegerQ,
 invariantBasis_List,
 covariantBasis_List
] :=

 Ceiling[1.1*Max@ListConvolve[dims[invariantBasis],dims[covariantBasis],1,0]/(2\[Nu]+1)]


extract[
 linearIndices_List,
 basis_List
] :=

 Module[
  {leafIndices,finalIndices,fullDimensions,leafDimensions},
  
  fullDimensions=Map[#[["dimensions"]]&,basis,{2}];(*degree; leaf; list of dimensions: interiorTensorTrains; SSYTs,tensorTrees for each \[Lambda]*)
  leafDimensions=Apply[Times,fullDimensions,{2}];
 
  leafIndices=
   MapThread[
    RaggedMultiIndex,
    {linearIndices,leafDimensions}
   ];(*degree; linearIndices; {index into leaf, linear index into interiorTensorTrains; SSYTs,tensorTrees for each \[Lambda]}*)
   
  finalIndices=
   MapThread[
    Function[{lIndices,dims},MapApply[{#1,ArrayMultiIndex[#2,dims[[#1]]]}&,lIndices]],
    {leafIndices,fullDimensions}
   ];(*degree; linearIndices; {index into leaf, multiindex into interiorTensorTrains; SSYTs,tensorTrees for each \[Lambda]}*)
  
  MapThread[
   Function[
    {indices,TensorProductBases},
    MapApply[
     <|
      "interiorTensorTrains"->{TensorProductBases[[#1]][["interiorTensorTrains"]][[First@#2]]},
      "SSYT\[Lambda]s"->MapThread[List@*Part,{TensorProductBases[[#1]][["SSYT\[Lambda]s"]],Rest[#2][[1;; ;;2]]}],
      "leafObjects"->
       MapThread[
        Function[
         {assoc,index},
         <|"interiorTensorTrains"->{assoc[["interiorTensorTrains"]][[index]]},"leafObjects"->{assoc[["leafObjects"]][[index]]}|>
        ],
        {TensorProductBases[[#1]][["leafObjects"]],Rest[#2][[2;; ;;2]]}
       ]
     |>&,
     indices
    ]
   ],
   {finalIndices,basis}
  ]
 ]


TensorProductBasis[
 {
  {
   \[Lambda]s_?DistinctPositiveIntegersQ,
   m\[Lambda]s_,
   \[Nu]_
  },
  D_,
  d\[Lambda]s_,
  \[Pi]\[Lambda]s_,
  \[Mu]\[Lambda]s_
 }
] :=

 With[
  {
   interiorTensorTrains=TensorTrainBasisTensorProduct[\[Mu]\[Lambda]s,\[Nu]],
   leafObjects=MapThread[TensorTreeBasisSchurPower,{\[Lambda]s,\[Pi]\[Lambda]s,\[Mu]\[Lambda]s}],
   SSYT\[Lambda]s=MapThread[SemiStandardYoungTableaux,{\[Pi]\[Lambda]s,m\[Lambda]s}]
  },
  {
   <|
    "interiorTensorTrains"->interiorTensorTrains,
    "leafObjects"->leafObjects,
    "SSYT\[Lambda]s"->SSYT\[Lambda]s,
    "dimensions"->Flatten[{Length@interiorTensorTrains,Transpose[{Length/@SSYT\[Lambda]s,Length@#[["leafObjects"]]&/@leafObjects}]}]
   |>
  }
 ]


EvaluateTensorProductBasis[
 basis_Association,
 inputVectors_List
] :=

 Module[
  {
   interiorVectors,
   outputVectors
  },

  (*inputVectors; \[Lambda]; SSYTs; tensorTrees; interiorVectors*)
  interiorVectors=Transpose@MapThread[EvaluateYoungSymmetrizedTensorTree,{basis[["leafObjects"]],basis[["SSYT\[Lambda]s"]],inputVectors}];

  (*inputVectors; interiorTensorTrains; SSYTs, tensorTrees for each \[Lambda]; outputVectors*)
  outputVectors=Outer[EvaluateTensorTrain[#1,List@##2]&,basis[["interiorTensorTrains"]],Sequence@@#,1,Sequence@@ConstantArray[2,Length@inputVectors]]&/@interiorVectors
 ]


(* ::Subsubsection:: *)
(*Public Functions*)


IsotypicDataTree[
 \[Lambda]s_?DistinctPositiveIntegersQ,
 m\[Lambda]s_?PositiveIntegersQ,
 \[Nu]_?NonNegativeIntegerQ,
 DMax_?NonNegativeIntegerQ
] /;
 Length@\[Lambda]s==Length@m\[Lambda]s :=

  Module[
   {tree},
   
   tree=Tree[{\[Lambda]s,m\[Lambda]s,\[Nu]},Range[0,DMax]];(*D*)
   
   tree=NestTree[WeakCompositions[#,Length[\[Lambda]s]]&,tree];(*d\[Lambda]s*)
   
   tree=NestTree[Tuples@ThinPartitions[#,\[Lambda]s,m\[Lambda]s]&,tree];(*\[Pi]\[Lambda]s*)
   
   tree=NestTree[ConstrainedIsotypicComponentsSchurPowers[\[Lambda]s,#,\[Nu]]&,tree];(*\[Mu]\[Lambda]s*)
   
   tree=PruneChildlessNodes[tree];
   
   AncestralNestTree[TensorProductBasis,tree](*TensorProductBasis*)
  ]


(*degree; leaf; TensorProductBasis*)
VectorSpaceBasis[
 \[Lambda]s_?DistinctPositiveIntegersQ,
 m\[Lambda]s_?PositiveIntegersQ,
 \[Nu]_?NonNegativeIntegerQ,
 DMax_?NonNegativeIntegerQ
] /;
 Length@\[Lambda]s==Length@m\[Lambda]s :=

  Lookup[
   Association[TreeData@#->TreeData/@TreeLeaves@#&/@TreeChildren@IsotypicDataTree[\[Lambda]s,m\[Lambda]s,\[Nu],DMax]],
   Range[0,DMax],
   {}
  ]


AlgebraBasis[
 \[Lambda]s_?DistinctPositiveIntegersQ,
 m\[Lambda]s_?PositiveIntegersQ,
 DMax_?NonNegativeIntegerQ
] /;
 Length@\[Lambda]s==Length@m\[Lambda]s :=

  Module[
   {
    VectorSpaceBasis=VectorSpaceBasis[\[Lambda]s,m\[Lambda]s,0,DMax],
    randomProbes,
    flattenLevels=flattenLevels[Length@\[Lambda]s],
    invariantSyndromes,
    productSyndromes,
    linearIndices
   },

   (*\[Lambda]; random probe; multiplicity; random vector*)
   randomProbes=generateRandomProbes[\[Lambda]s,m\[Lambda]s,algebraDimensionBound[VectorSpaceBasis]];
   
   (*degree; leaf; random probe; interiorTensorTrains; SSYTs, tensorTrees for each \[Lambda]; output vector*)
   invariantSyndromes=EvaluateBasis[VectorSpaceBasis,randomProbes];
   
   (*degree; random probe; leaf, interiorTensorTrains, SSYTs, tensorTrees for each \[Lambda]; output vector*)
   invariantSyndromes=Flatten[invariantSyndromes,flattenLevels];

   (*degree; random probe; columns*)
   productSyndromes=
    Table[
      RowJoin@@Table[
       RowKroneckerProduct[invariantSyndromes[[i]],invariantSyndromes[[d+1-i]]],
       {i,Ceiling[d/2],1,-1}
      ],
      {d,1,DMax+1}
     ];
    
   (*indices into productSyndromes*)
   linearIndices=PivotColumns/@productSyndromes;
   
   (*indices into invariantSyndromes*)
   linearIndices=
    MapThread[
     DeleteCases[#1,i_/;i<=#2]-#2&,
     {linearIndices,Last@*Dimensions/@productSyndromes-Last@*Most@*Dimensions/@invariantSyndromes}
    ];
   
   extract[linearIndices,VectorSpaceBasis]
  ]


ModuleBasis[
 \[Lambda]s_?DistinctPositiveIntegersQ,
 m\[Lambda]s_?PositiveIntegersQ,
 \[Nu]_?PositiveIntegerQ,
 DMax_?NonNegativeIntegerQ
] /;
 Length@\[Lambda]s==Length@m\[Lambda]s :=

  Module[
   {
    InvariantVectorSpaceBasis=VectorSpaceBasis[\[Lambda]s,m\[Lambda]s,0,DMax],
    CovariantVectorSpaceBasis=VectorSpaceBasis[\[Lambda]s,m\[Lambda]s,\[Nu],DMax],
    randomProbes,
    flattenLevels=flattenLevels[Length@\[Lambda]s],
    invariantSyndromes,
    covariantSyndromes,
    productSyndromes,
    linearIndices
   },

   randomProbes=generateRandomProbes[\[Lambda]s,m\[Lambda]s,moduleDimensionBound[\[Nu],InvariantVectorSpaceBasis,CovariantVectorSpaceBasis]];

   invariantSyndromes=EvaluateBasis[InvariantVectorSpaceBasis,randomProbes];
   invariantSyndromes=Flatten[invariantSyndromes,flattenLevels];

   covariantSyndromes=EvaluateBasis[CovariantVectorSpaceBasis,randomProbes];
   covariantSyndromes=Flatten[covariantSyndromes,flattenLevels];

   productSyndromes=
     ListConvolve[
      invariantSyndromes,
      covariantSyndromes,
      1,
      {{{{}}}},
      RowKroneckerProduct,
      RowJoin
     ];
   
   linearIndices=PivotColumns/@productSyndromes;

   (*indices into covariantSyndromes*)
   linearIndices=
    MapThread[
     DeleteCases[#1,i_/;i<=#2]-#2&,
     {linearIndices,Last@*Dimensions/@productSyndromes-Last@*Most@*Dimensions/@covariantSyndromes}
    ];

   extract[linearIndices,CovariantVectorSpaceBasis]
  ]


EvaluateBasis[
 VectorSpaceBasis_List,
 inputVectors_List
] :=

 Map[
  EvaluateTensorProductBasis[#,inputVectors]&,
  VectorSpaceBasis,
  {2}
 ]


End[];


EndPackage[];
