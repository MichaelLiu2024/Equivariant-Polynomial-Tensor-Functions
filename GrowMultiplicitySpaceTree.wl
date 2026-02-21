(* ::Package:: *)

BeginPackage["GrowMultiplicitySpaceTree`",{"TreeTools`","TensorTools`","ClebschGordanTools`","IsotypicDecompositionTools`","CombinatoricsTools`"}];


IsotypicDataTree
IsotypicDataTreeToVectorSpaceBases
VectorSpaceBasesToAlgebraBases
EvaluateVectorSpaceBases
SphericalBasisToMonomialBasis
generateVariables


Begin["`Private`"];


SetAttributes[generateVariables,Listable]
generateVariables[\[Lambda]_Integer?Positive,m\[Lambda]_Integer?Positive]:={Table[Global`x[\[Lambda]][multiplicity][m],{multiplicity,1,m\[Lambda]},{m,-\[Lambda],\[Lambda]}]}


(*https://resources.wolframcloud.com/FunctionRepository/resources/SolidHarmonicR/*)
SolidHarmonicR[l_Integer?NonNegative,m_Integer,x_,y_,z_]/;Abs[m]<=l:=
 N@With[
  {dpower=If[#2==0,1,#1^#2]&,s=Sign[m],am=Abs[m]},
  
  (-1)^((1-s)am/2)Sqrt[(l-am)!/(l+am)!]dpower[x+I s y,am]*
  Sum[
   (-1)^((l+am)/2-k)(l+am+2k-1)!!dpower[z,2k]dpower[x^2+y^2+z^2,(l-am)/2-k]/((2k)!(l-am-2k)!!),
   {k,Mod[l-am,2]/2,(l-am)/2},
   Method->"Procedural"
  ]
 ]


EnumerateTensorProductBases[{{\[Lambda]s_,m\[Lambda]s_,\[Nu]_,DMax_},D_,d\[Lambda]s_,\[Pi]\[Lambda]s_,\[Mu]\[Lambda]s_}]:=
 {
  <|
   "interiorTensorTrains"->TensorTrainBasisTensorProduct[\[Mu]\[Lambda]s,\[Nu]],
   "leafObjects"->MapThread[TensorTreeBasisSchurPower,{\[Lambda]s,\[Pi]\[Lambda]s,\[Mu]\[Lambda]s}],
   "SSYT\[Lambda]s"->MapThread[SemiStandardYoungTableaux,{\[Pi]\[Lambda]s,m\[Lambda]s}]
  |>
 }


HarmonicTensorCoordinates[\[Lambda]_Integer?Positive,m_Integer]:=HarmonicTensorCoordinates[\[Lambda],m]=
 Total@ReplaceAll[
  CoefficientRules[SolidHarmonicR[\[Lambda],m,x,y,z],{x,y,z}],
  (powers_->coefficients_):>coefficients*x[Sequence@@Join@@MapThread[ConstantArray,{Range[3],powers}]]
 ]


SphericalBasisToMonomialBasis[sphericalPolynomials_]:=
 ReplaceAll[
  sphericalPolynomials,
  Global`x[\[Lambda]_][multiplicity_][m_]:>(HarmonicTensorCoordinates[\[Lambda],m]/.x[indices__]:>Global`x[\[Lambda]][multiplicity][indices])
 ]


IsotypicDataTreeToVectorSpaceBases[tree_Tree]:=
 Lookup[
  Association[TreeData@#->TreeData/@TreeLeaves@#&/@TreeChildren@tree],
  Range[0,TreeData[tree][[4]]],
  {}
 ]


EvaluateTensorProductBases[bases_Association,inputVectors_List]:=
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
  outputVectors=Outer[EvaluateTensorTrain,bases[["interiorTensorTrains"]],Sequence@@#,1,Sequence@@ConstantArray[2,Length@inputVectors]]&/@interiorVectors
 ]


EvaluateVectorSpaceBases[VectorSpaceBases_List,inputVectors_List]:=
 Map[
  EvaluateTensorProductBases[#,inputVectors]&,
  VectorSpaceBases,
  {2}
 ]


VectorSpaceBasesToAlgebraBases[\[Lambda]s_List,m\[Lambda]s_List,DMax_Integer?Positive,VectorSpaceBases_List]:=
 Module[
  {
   randomProbes,
   rowIndices,
   columnIndices,
   basisSyndromes,basisDimensions,
   productSyndromes,productDimensions,
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
    Function[{\[Lambda],m\[Lambda]},RandomReal[1,{Binomial[2*Max@\[Lambda]s+DMax,DMax](*worse case sampling; may need oversampling*),m\[Lambda],2\[Lambda]+1}]],
    {\[Lambda]s,m\[Lambda]s}
   ];
   
  (*
  Level 1: degree
  Level 2: leaf of subtree
  Level 3: random probe
  Level 4: interiorTensorTrains
  Level 5 through 4+2n: SSYTs,tensorTrees for each \[Lambda]
  Object:  output vector
  *)
  basisSyndromes=EvaluateVectorSpaceBases[VectorSpaceBases,randomProbes];
  
  rowIndices={3,5+2*Length@\[Lambda]s};
  columnIndices=Complement[Range[5+2*Length@\[Lambda]s],rowIndices,{1}];
  
  (*
  Level 1: degree (0,...,DMax)
  Level 2: random probe, output
  Level 3: interiorTensorTrains; SSYTs,tensorTrees for each \[Lambda]
  Object:  syndrome scalar
  *)
  basisSyndromes=Flatten[basisSyndromes,{{1},rowIndices,columnIndices}];
  
  basisDimensions=Last@*Dimensions/@basisSyndromes;
  
  (*use convolution for covariants*)
  (*productSyndromes=
   ListConvolve[
    basisSyndromes,(*invariants*)
    basisSyndromes,(*covariants*)
    1,
    {{{}}},
    RowKroneckerProduct,
    RowJoin
   ];*)

  productSyndromes=
   Table[
    RowJoin@@MapThread[
     RowKroneckerProduct,
     {Reverse@Take[basisSyndromes,Ceiling[d/2]],Take[basisSyndromes,{d+1-Ceiling[d/2],d}]}
    ],
    {d,1,Length@basisSyndromes}
   ];

  Echo@*Dimensions/@productSyndromes;

  productDimensions=Last@*Dimensions/@productSyndromes;
  
  (*indices into productSyndromes*)
  linearIndices=PivotColumns/@productSyndromes;
  
  (*indices into basisSyndromes*)
  linearIndices=
   MapThread[
    DeleteCases[#1,i_/;i<=#2]-#2&,
    {linearIndices,productDimensions-basisDimensions}
   ];
  
  (*
  Level 1: degree
  Level 2: leaf of subtree
  Object:  list of dimensions: interiorTensorTrains; SSYTs,tensorTrees for each \[Lambda]
  *)
  fullDimensions=Map[TPDimensions,VectorSpaceBases,{2}];
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
   {finalIndices,VectorSpaceBases}
  ]
 ]


TreeDimensions[tree_Association]:=Length@tree[["leafObjects"]]
TPDimensions[TensorProductBases_Association]:=
 Flatten[
  {
   Length@TensorProductBases[["interiorTensorTrains"]],
   Transpose[{Length/@TensorProductBases[["SSYT\[Lambda]s"]],TreeDimensions/@TensorProductBases[["leafObjects"]]}]
  }
 ]


RowKroneckerProduct[m1_List?MatrixQ,{{}}]:={{}}
RowKroneckerProduct[{{}},m2_List?MatrixQ]:={{}}
RowKroneckerProduct[m1_List?MatrixQ,m2_List?MatrixQ]/;Length@m1==Length@m2:=MapThread[Flatten@*KroneckerProduct,{m1,m2}]


RowJoin[ms__]:=Join[ms,2]


SO3RepresentationQ[\[Lambda]s_List,m\[Lambda]s_List]:=
 VectorQ[\[Lambda]s,Positive]\[And]
 VectorQ[m\[Lambda]s,Positive]\[And]
 Length[\[Lambda]s]==Length[m\[Lambda]s]\[And]
 DuplicateFreeQ[\[Lambda]s]


IsotypicDataTree[\[Lambda]s_List,m\[Lambda]s_List,\[Nu]_Integer?NonNegative,DMax_Integer?Positive]/;
 SO3RepresentationQ[\[Lambda]s,m\[Lambda]s]:=
  Module[
   {tree},
   
   (*Level 1: D*)
   tree=Tree[{\[Lambda]s,m\[Lambda]s,\[Nu],DMax},Range[0,DMax]];
   
   (*Level 2: d\[Lambda]s*)
   tree=NestTree[WeakCompositions[#,Length[\[Lambda]s]]&,tree];
   
   (*Level 3: \[Pi]\[Lambda]s*)
   tree=NestTree[Tuples@ThinPartitions[#,\[Lambda]s,m\[Lambda]s]&,tree];
   
   (*Level 4: \[Mu]\[Lambda]s*)
   tree=NestTree[ConstrainedIsotypicComponentsSchurPowers[\[Lambda]s,#,\[Nu]]&,tree];
   
   (*Prune childless nodes for memory efficiency*)
   tree=PruneChildlessNodes[tree];
   
   (*Level 5: interiorTensorTrains, leafObjects, and SSYT\[Lambda]s*)
   AncestralNestTree[EnumerateTensorProductBases,tree]
  ]


End[];


EndPackage[];
