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


TensorProductBasisDimensions[TensorProductBasis_Association]:=
 Flatten[
  {
   Length@TensorProductBasis[["interiorTensorTrains"]],
   Transpose[{Length/@TensorProductBasis[["SSYT\[Lambda]s"]],Length@#[["leafObjects"]]&/@TensorProductBasis[["leafObjects"]]}]
  }
 ]


RowKroneckerProduct[m1_List?MatrixQ,{{}}]:={{}}
RowKroneckerProduct[{{}},m2_List?MatrixQ]:={{}}
RowKroneckerProduct[m1_List?MatrixQ,m2_List?MatrixQ]/;Length@m1==Length@m2:=MapThread[Flatten@*KroneckerProduct,{m1,m2}]


RowJoin[ms__]:=Join[ms,2]


TensorProductBasis[{{\[Lambda]s_,m\[Lambda]s_,\[Nu]_},D_,d\[Lambda]s_,\[Pi]\[Lambda]s_,\[Mu]\[Lambda]s_}]:=
 {
  <|
   "interiorTensorTrains"->TensorTrainBasisTensorProduct[\[Mu]\[Lambda]s,\[Nu]],
   "leafObjects"->MapThread[TensorTreeBasisSchurPower,{\[Lambda]s,\[Pi]\[Lambda]s,\[Mu]\[Lambda]s}],
   "SSYT\[Lambda]s"->MapThread[SemiStandardYoungTableaux,{\[Pi]\[Lambda]s,m\[Lambda]s}]
  |>
 }


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


AlgebraBasis[\[Lambda]s_List,m\[Lambda]s_List,DMax_Integer?NonNegative]/;
 SO3RepresentationQ[\[Lambda]s,m\[Lambda]s]:=
  Module[
   {
    VectorSpaceBasis=VectorSpaceBasis[\[Lambda]s,m\[Lambda]s,0,DMax],
    randomProbes,
    invariantSyndromes,
    productSyndromes,
    linearIndices,leafIndices,finalIndices,
    fullDimensions,leafDimensions
   },
  
  (*
  Level 1: \[Lambda]
  Level 2: random probe
  Level 3: multiplicity
  Object:  random vector
  *)
  randomProbes=
   MapThread[
    Function[{\[Lambda],m\[Lambda]},RandomReal[1,{Binomial[2*Max@\[Lambda]s+DMax,DMax]+DMax,m\[Lambda],2\[Lambda]+1}]],
    {\[Lambda]s,m\[Lambda]s}
   ];
   
  (*
  Level 1: degree
  Level 2: leaf
  Level 3: random probe
  Level 4: interiorTensorTrains
  Level 5 through 4+2n: SSYTs,tensorTrees for each \[Lambda]
  Object:  output vector
  *)
  invariantSyndromes=EvaluateBasis[VectorSpaceBasis,randomProbes];
  
  (*
  Level 1: degree (0,...,DMax)
  Level 2: random probe, output
  Level 3: interiorTensorTrains; SSYTs,tensorTrees for each \[Lambda]
  Object:  syndrome scalar
  *)
  invariantSyndromes=
   Flatten[
    invariantSyndromes,
    {{1},{3,5+2*Length@\[Lambda]s},Complement[Range[5+2*Length@\[Lambda]s],{3,5+2*Length@\[Lambda]s},{1}]}
   ];

  productSyndromes=
   Table[
    RowJoin@@MapThread[
     RowKroneckerProduct,
     {Reverse@Take[invariantSyndromes,Ceiling[d/2]],Take[invariantSyndromes,{d+1-Ceiling[d/2],d}]}
    ],
    {d,1,DMax+1}
   ];
  
  (*indices into productSyndromes*)
  linearIndices=PivotColumns/@productSyndromes;
  
  (*indices into invariantSyndromes*)
  linearIndices=
   MapThread[
    DeleteCases[#1,i_/;i<=#2]-#2&,
    {linearIndices,Last@*Dimensions/@productSyndromes-Last@*Dimensions/@invariantSyndromes}
   ];
  
  (*
  Level 1: degree
  Level 2: leaf of subtree
  Object:  list of dimensions: interiorTensorTrains; SSYTs,tensorTrees for each \[Lambda]
  *)
  fullDimensions=Map[TensorProductBasisDimensions,VectorSpaceBasis,{2}];
  leafDimensions=Apply[Times,fullDimensions,{2}];
  
  (*
  Level 1: degree
  Level 2: linearIndices
  Object:  {index into leaf, linear index into interiorTensorTrains; SSYTs,tensorTrees for each \[Lambda]}
  *)
  leafIndices=
   MapThread[
    linearIndicesToRaggedMultiIndices,
    {linearIndices,leafDimensions}
   ];
   
  (*
  Level 1: degree
  Level 2: linearIndices
  Object:  {index into leaf, multiindex into interiorTensorTrains; SSYTs,tensorTrees for each \[Lambda]}
  *)
  finalIndices=
   MapThread[
    Function[{lIndices,dims},MapApply[{#1,linearIndexToArrayMultiIndex[#2,dims[[#1]]]}&,lIndices]],
    {leafIndices,fullDimensions}
   ];
  (*I can probably write a single subfunction to do all of this!*)

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
   {finalIndices,VectorSpaceBasis}
  ]
 ]


ModuleBasis[\[Lambda]s_List,m\[Lambda]s_List,DMax_Integer?NonNegative]/;
 SO3RepresentationQ[\[Lambda]s,m\[Lambda]s]:=
  Module[
   {
    invariantSyndromes,
    covariantSyndromes,
    productSyndromes
   },
   
   productSyndromes=
    ListConvolve[
     invariantSyndromes,
     covariantSyndromes,
     1,
     {{{}}},
     RowKroneckerProduct,
     RowJoin
    ];
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
