(* ::Package:: *)

BeginPackage["GrowMultiplicitySpaceTree`",{"TreeTools`","TensorTools`","ClebschGordanTools`","IsotypicDecompositionTools`","CombinatoricsTools`"}];


IsotypicDataTree
IsotypicDataTreeToVectorSpaceBases
VectorSpaceBasesToAlgebraBases


Begin["`Private`"];


EnumerateTensorProductBases[{{\[Lambda]s_,m\[Lambda]s_,\[Nu]_,DMax_},D_,d\[Lambda]s_,\[Pi]\[Lambda]s_,\[Mu]\[Lambda]s_}]:=
 {
  <|
   "interiorTensorTrains"->TensorTrainBasisTensorProduct[\[Mu]\[Lambda]s,\[Nu]],
   "leafObjects"->MapThread[TensorTreeBasisSchurPower,{\[Lambda]s,\[Pi]\[Lambda]s,\[Mu]\[Lambda]s}],
   "SSYT\[Lambda]s"->MapThread[SemiStandardYoungTableaux,{\[Pi]\[Lambda]s,m\[Lambda]s}]
  |>
 }


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


HarmonicTensorCoordinates[\[Lambda]_Integer?Positive,m_Integer]:=HarmonicTensorCoordinates[\[Lambda],m]=
 Total@ReplaceAll[
  CoefficientRules[SolidHarmonicR[\[Lambda],m,x,y,z],{x,y,z}],
  (powers_->coefficients_):>coefficients*x[Sequence@@Join@@MapThread[ConstantArray,{Range[3],powers}]]
 ]


SphericalBasisToMonomialBasis[sphericalPolynomials_]:=
 ReplaceAll[
  sphericalPolynomials,
  Global`x[\[Lambda]_][m_][multiplicity_]:>(HarmonicTensorCoordinates[\[Lambda],m]/.x[indices__]:>Global`x[\[Lambda]][multiplicity][indices])
 ]


SetAttributes[generateVariables,Listable]
generateVariables[\[Lambda]_Integer?Positive,m\[Lambda]_Integer?Positive]:=Table[Global`x[\[Lambda]][m][multiplicity],{multiplicity,1,m\[Lambda]},{m,-\[Lambda],\[Lambda]}]


IsotypicDataTreeToVectorSpaceBases[tree_Tree]:=
 Lookup[
  Association[TreeData@#->TreeData/@TreeLeaves@#&/@TreeChildren@tree],
  Range[TreeData[tree][[4]]],
  {}
 ]


EvaluateVectorSpaceBasis[bases_Association,inputVectors_List]:=
 Module[
  {
   interiorVectors,
   outputVectors
  },

  (*
  Level 1: \[Lambda]
  Level 2: inputVectors
  Level 3: SSYTs
  Level 4: tensorTrees
  Object:  interiorVectors
  *)
  interiorVectors=MapThread[EvaluateYoungSymmetrizedTensorTree,{bases[["leafObjects"]],bases[["SSYT\[Lambda]s"]],inputVectors}];

  (*
  Level 1: interiorTensorTrains
  Level 2 through 1+3n: inputVectors,SSYTs,tensorTrees for each \[Lambda]
  Object:  outputVectors in Subscript[H, \[Nu]]
  *)
  outputVectors=Outer[EvaluateTensorTrain,bases[["interiorTensorTrains"]],Sequence@@interiorVectors,1,Sequence@@ConstantArray[3,Length@inputVectors]]
 ]


EvaluateVectorSpaceBases[VectorSpaceBases_List,inputVectors_List]:=
 Map[
  EvaluateVectorSpaceBasis[#,inputVectors]&,
  VectorSpaceBases,
  {2}
 ]


VectorSpaceBasesToAlgebraBases[\[Lambda]s_List,m\[Lambda]s_List,DMax_Integer?Positive,VectorSpaceBases_List]:=
 Module[
  {
   randomProbes,
   syndromeMatrix,
   rowIndices,
   columnIndices,
   linearIndices
  },
  
  (*
  Level 1: \[Lambda]
  Level 2: random probe
  Level 3: multiplicity
  Object:  random vector
  *)
  randomProbes=
   MapThread[
    Function[{\[Lambda],m\[Lambda]},RandomReal[1,{DMax+DMax(*oversampling*),m\[Lambda],2\[Lambda]+1}]],
    {\[Lambda]s,m\[Lambda]s}
   ];
   
  (*
  Level 1: degree
  Level 2: leaf of subtree
  Level 3: interiorTensorTrains
  Level 4 through 3+3n: inputVectors,SSYTs,tensorTrees for each \[Lambda]
  Object:  random vector
  *)
  syndromeMatrix=EvaluateVectorSpaceBases[VectorSpaceBases,randomProbes];
  
  rowIndices=4+3*Range[0,Length@\[Lambda]s];
  columnIndices=Complement[Range[4+3*Length@\[Lambda]s],rowIndices,{1}];
  
  (*Actually, you're supposed to multiply lower degree syndromes and compare them to the higher degree ones...*)
  
  syndromeMatrix=Flatten[syndromeMatrix,{{1},rowIndices,columnIndices}];
  
  syndromeMatrix
 ]


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
   tree=Tree[{\[Lambda]s,m\[Lambda]s,\[Nu],DMax},Range@DMax];
   
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
