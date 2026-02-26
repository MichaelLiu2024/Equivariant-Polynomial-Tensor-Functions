(* ::Package:: *)

BeginPackage["GrowMultiplicitySpaceTree`",{"TreeTools`","TensorTools`","ClebschGordanTools`","IsotypicDecompositionTools`","CombinatoricsTools`"}];


IsotypicDataTree
VectorSpaceBasis
AlgebraBasis
ModuleBasis
EvaluateBasis


Begin["`Private`"];


(* ::Subsubsection:: *)
(*Private Functions*)


SO3RepresentationQ[\[Lambda]s_List,m\[Lambda]s_List]:=
 VectorQ[\[Lambda]s,Positive]\[And]
 VectorQ[m\[Lambda]s,Positive]\[And]
 Length[\[Lambda]s]==Length[m\[Lambda]s]\[And]
 DuplicateFreeQ[\[Lambda]s]


(*Store dimensions in here so we don't need the next function?*)
TensorProductBasis[{{\[Lambda]s_,m\[Lambda]s_,\[Nu]_},D_,d\[Lambda]s_,\[Pi]\[Lambda]s_,\[Mu]\[Lambda]s_}]:=
 {
  <|
   "interiorTensorTrains"->TensorTrainBasisTensorProduct[\[Mu]\[Lambda]s,\[Nu]],
   "leafObjects"->MapThread[TensorTreeBasisSchurPower,{\[Lambda]s,\[Pi]\[Lambda]s,\[Mu]\[Lambda]s}],
   "SSYT\[Lambda]s"->MapThread[SemiStandardYoungTableaux,{\[Pi]\[Lambda]s,m\[Lambda]s}]
  |>
 }


TensorProductBasisDimensions[TensorProductBasis_Association]:=
 Flatten[
  {
   Length@TensorProductBasis[["interiorTensorTrains"]],
   Transpose[{Length/@TensorProductBasis[["SSYT\[Lambda]s"]],Length@#[["leafObjects"]]&/@TensorProductBasis[["leafObjects"]]}]
  }
 ]


RowKroneckerProduct[m1_List?ArrayQ,{{{}}}]:={{}}
RowKroneckerProduct[{{{}}},m2_List?ArrayQ]:={{}}
RowKroneckerProduct[m1_List?ArrayQ,m2_List?ArrayQ]/;
 Length@m1==Length@m2\[And]Depth@m1==4==Depth@m2:=
  Flatten[
   MapThread[KroneckerProduct,{m1,m2}],
   {{1,3},{2}}
  ]


RowJoin[ms__]:=Join[ms,2]


(* ::Subsubsection:: *)
(*Public Functions*)


IsotypicDataTree[\[Lambda]s_List,m\[Lambda]s_List,\[Nu]_Integer?NonNegative,DMax_Integer?NonNegative]/;
 SO3RepresentationQ[\[Lambda]s,m\[Lambda]s]:=
  Module[
   {tree},
   
   tree=Tree[{\[Lambda]s,m\[Lambda]s,\[Nu]},Range[0,DMax]];(*D*)
   
   tree=NestTree[WeakCompositions[#,Length[\[Lambda]s]]&,tree];(*d\[Lambda]s*)
   
   tree=NestTree[Tuples@ThinPartitions[#,\[Lambda]s,m\[Lambda]s]&,tree];(*\[Pi]\[Lambda]s*)
   
   tree=NestTree[ConstrainedIsotypicComponentsSchurPowers[\[Lambda]s,#,\[Nu]]&,tree];(*\[Mu]\[Lambda]s*)
   
   tree=PruneChildlessNodes[tree];
   
   AncestralNestTree[TensorProductBasis,tree](*TensorProductBasis*)
  ]


(*Level 1: degree*)
(*Level 2: leaf*)
(*Object:  TensorProductBasis*)
VectorSpaceBasis[\[Lambda]s_List,m\[Lambda]s_List,\[Nu]_Integer?NonNegative,DMax_Integer?NonNegative]/;
 SO3RepresentationQ[\[Lambda]s,m\[Lambda]s]:=
  Lookup[
   Association[TreeData@#->TreeData/@TreeLeaves@#&/@TreeChildren@IsotypicDataTree[\[Lambda]s,m\[Lambda]s,\[Nu],DMax]],
   Range[0,DMax],
   {}
  ]


randomProbes[\[Lambda]s_List,m\[Lambda]s_List,DMax_Integer?NonNegative]/;
 SO3RepresentationQ[\[Lambda]s,m\[Lambda]s]:=
  MapThread[
   Function[{\[Lambda],m\[Lambda]},RandomReal[1,{Binomial[2*Max@\[Lambda]s+DMax,DMax]+DMax,m\[Lambda],2\[Lambda]+1}]],
   {\[Lambda]s,m\[Lambda]s}
  ]


flattenLevels[n_Integer?Positive]:=
 With[
  {maxLvl=5+2*n},
  {{1},{3},Complement[Range@maxLvl,{1,3,maxLvl}],{maxLvl}}
 ];


AlgebraBasis[\[Lambda]s_List,m\[Lambda]s_List,DMax_Integer?NonNegative]/;
 SO3RepresentationQ[\[Lambda]s,m\[Lambda]s]:=
  Module[
   {
    VectorSpaceBasis=VectorSpaceBasis[\[Lambda]s,m\[Lambda]s,0,DMax],
    randomProbes=randomProbes[\[Lambda]s,m\[Lambda]s,DMax],(*\[Lambda]; random probe; multiplicity; random vector*)
    flattenLevels=flattenLevels[Length@\[Lambda]s],
    invariantSyndromes,
    productSyndromes,
    linearIndices
   },
   
   invariantSyndromes=EvaluateBasis[VectorSpaceBasis,randomProbes];(*degree; leaf; random probe; interiorTensorTrains; SSYTs, tensorTrees for each \[Lambda]; output vector*)
   
   invariantSyndromes=Flatten[invariantSyndromes,flattenLevels];(*degree; random probe; leaf, interiorTensorTrains, SSYTs, tensorTrees for each \[Lambda]; output vector*)

   productSyndromes=
    Table[
     RowJoin@@Table[
      RowKroneckerProduct[invariantSyndromes[[i]],invariantSyndromes[[d+1-i]]],
      {i,Ceiling[d/2],1,-1}
     ],
     {d,1,DMax+1}
    ];(*degree; random probe; columns*)
    
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


ModuleBasis[\[Lambda]s_List,m\[Lambda]s_List,\[Nu]_Integer?Positive,DMax_Integer?NonNegative]/;
 SO3RepresentationQ[\[Lambda]s,m\[Lambda]s]:=
  Module[
   {
    InvariantVectorSpaceBasis=VectorSpaceBasis[\[Lambda]s,m\[Lambda]s,0,DMax],
    CovariantVectorSpaceBasis=VectorSpaceBasis[\[Lambda]s,m\[Lambda]s,\[Nu],DMax],
    randomProbes=randomProbes[\[Lambda]s,m\[Lambda]s,DMax],
    flattenLevels=flattenLevels[Length@\[Lambda]s],
    invariantSyndromes,
    covariantSyndromes,
    productSyndromes,
    linearIndices
   },

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


extract[linearIndices_List?VectorQ,basis_List]:=
 Module[
  {leafIndices,finalIndices,fullDimensions,leafDimensions},
  
  fullDimensions=Map[TensorProductBasisDimensions,basis,{2}];(*degree; leaf; list of dimensions: interiorTensorTrains; SSYTs,tensorTrees for each \[Lambda]*)
  leafDimensions=Apply[Times,fullDimensions,{2}];
 
  leafIndices=
   MapThread[
    linearIndicesToRaggedMultiIndices,
    {linearIndices,leafDimensions}
   ];(*degree; linearIndices; {index into leaf, linear index into interiorTensorTrains; SSYTs,tensorTrees for each \[Lambda]}*)
   
  finalIndices=
   MapThread[
    Function[{lIndices,dims},MapApply[{#1,linearIndexToArrayMultiIndex[#2,dims[[#1]]]}&,lIndices]],
    {leafIndices,fullDimensions}
   ];(*degree; linearIndices; {index into leaf, multiindex into interiorTensorTrains; SSYTs,tensorTrees for each \[Lambda]}*)
  
  MapThread[
   Function[
    {indices,bases},
    MapApply[
     <|
      "interiorTensorTrains"->{bases[[#1]][["interiorTensorTrains"]][[First@#2]]},
      "SSYT\[Lambda]s"->MapThread[List@*Part,{bases[[#1]][["SSYT\[Lambda]s"]],Rest[#2][[1;; ;;2]]}],
      "leafObjects"->
       MapThread[
        Function[
         {assoc,index},
         <|"interiorTensorTrains"->{assoc[["interiorTensorTrains"]][[index]]},"leafObjects"->{assoc[["leafObjects"]][[index]]}|>
        ],
        {bases[[#1]][["leafObjects"]],Rest[#2][[2;; ;;2]]}
       ]
     |>&,
     indices
    ]
   ],
   {finalIndices,basis}
  ]
 ]


EvaluateTensorProductBasis[bases_Association,inputVectors_List]:=
 Module[
  {
   interiorVectors,
   outputVectors
  },

  (*
  Level 1: inputVectors
  Level 2: \[Lambda]
  Level 3: SSYTs
  Level 4: tensorTrees
  Object:  interiorVectors
  *)
  interiorVectors=Transpose@MapThread[EvaluateYoungSymmetrizedTensorTree,{bases[["leafObjects"]],bases[["SSYT\[Lambda]s"]],inputVectors}];

  (*
  Level 1: inputVectors
  Level 2: interiorTensorTrains
  Level 3 through 2+2n: SSYTs,tensorTrees for each \[Lambda]
  Object:  outputVectors in Subscript[H, \[Nu]]
  *)
  outputVectors=Outer[EvaluateTensorTrain[#1,List@##2]&,bases[["interiorTensorTrains"]],Sequence@@#,1,Sequence@@ConstantArray[2,Length@inputVectors]]&/@interiorVectors
 ]


EvaluateBasis[VectorSpaceBasis_List,inputVectors_List]:=
 Map[
  EvaluateTensorProductBasis[#,inputVectors]&,
  VectorSpaceBasis,
  {2}
 ]


End[];


EndPackage[];
