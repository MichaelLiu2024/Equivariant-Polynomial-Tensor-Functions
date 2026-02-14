(* ::Package:: *)

BeginPackage["GrowMultiplicitySpaceTree`",{"TreeTools`","TensorTools`","ClebschGordanTools`","IsotypicDecompositionTools`","CombinatoricsTools`"}];


IsotypicDataTree
EnumerateVectorSpaceBases


Begin["`Private`"];


EnumerateTensorProductBases[{{\[Lambda]s_,m\[Lambda]s_,\[Nu]_},D_,d\[Lambda]s_,\[Pi]\[Lambda]s_,\[Mu]\[Lambda]s_}]:=
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


HarmonicTensorCoordinates[\[Lambda]_Integer?NonNegative,m_Integer]:=HarmonicTensorCoordinates[\[Lambda],m]=
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
generateVariables[\[Lambda]_Integer?NonNegative,m\[Lambda]_Integer?Positive]:=Table[Global`x[\[Lambda]][m][multiplicity],{multiplicity,1,m\[Lambda]},{m,-\[Lambda],\[Lambda]}]


FormPolynomials[bases_Association,variables_List]:=
 Module[
  {
   interiorVectors,
   sphericalPolynomials
  },

  (*
  Level 1: \[Lambda]
  Level 2: basis elements
  Object:  interiorVectors
  *)
  interiorVectors=MapThread[EvaluateYoungSymmetrizedTensorTree,{bases[["leafObjects"]],bases[["SSYT\[Lambda]s"]],variables}];

  sphericalPolynomials=Flatten[Outer[EvaluateTensorTrain,bases[["interiorTensorTrains"]],Tuples@interiorVectors,1],1]
 ]


FormPolynomials[,generateVariables[##]]
SphericalBasisToMonomialBasis[sphericalPolynomials]


(*find a better way to sort these; maybe just pad degrees and Transpose...*)
EnumerateVectorSpaceBases[\[Lambda]s_List,m\[Lambda]s_List,\[Nu]_Integer?NonNegative,DMax_Integer?Positive]/;
 SO3RepresentationQ[\[Lambda]s,m\[Lambda]s]:=
  Flatten@MapThread[
   HarvestIsotypicDataTree@IsotypicDataTree[##,\[Nu],DMax]&,
   {Subsets[\[Lambda]s,{1,\[Infinity]}],Subsets[m\[Lambda]s,{1,\[Infinity]}]}
  ]


HarvestIsotypicDataTree[tree_Tree]:=<|"\[Lambda]s"->TreeData[tree][[1]],"m\[Lambda]s"->TreeData[tree][[2]],"D"->TreeData@#,"IsotypicData"->TreeData/@TreeLeaves@#|>&/@TreeChildren@tree


(* ::Subsection:: *)
(*Public Function Implementations*)


(*Then, write a function to multiply all lower degree invariants and do pivot finding to get independent higher degree invariants. you can do simple checks like toss out zeros, and if there is nothing left, you are already done!*)


SO3RepresentationQ[\[Lambda]s_List,m\[Lambda]s_List]:=
 VectorQ[\[Lambda]s,Positive]\[And]
 VectorQ[m\[Lambda]s,Positive]\[And]
 Length[\[Lambda]s]==Length[m\[Lambda]s]\[And]
 DuplicateFreeQ[\[Lambda]s]


IsotypicDataTree[\[Lambda]s_List,m\[Lambda]s_List,\[Nu]_Integer?NonNegative,DMax_Integer?Positive]/;
 SO3RepresentationQ[\[Lambda]s,m\[Lambda]s]:=
  Module[
   {tree},
   
   If[Length@\[Lambda]s>DMax,Return[Tree[{\[Lambda]s,m\[Lambda]s,\[Nu]},{}]]];
   
   (*Level 1: D*)
   tree=Tree[{\[Lambda]s,m\[Lambda]s,\[Nu]},Range[Length@\[Lambda]s,DMax]];
   
   (*Level 2: d\[Lambda]s*)
   tree=NestTree[StrictCompositions[#,Length[\[Lambda]s]]&,tree];
   
   (*Level 3: \[Pi]\[Lambda]s*)
   tree=NestTree[Tuples@ThinPartitions[#,\[Lambda]s,m\[Lambda]s]&,tree];
   
   (*Level 4: \[Mu]\[Lambda]s*)
   tree=NestTree[ConstrainedIsotypicComponentsSchurPowers[\[Lambda]s,#,\[Nu]]&,tree];
   
   (*Prune childless nodes for memory efficiency*)
   tree=PruneChildlessNodes[tree];
   
   If[tree===Nothing,Return[Tree[{\[Lambda]s,m\[Lambda]s,\[Nu]},{}]]];
   
   (*Level 5: interiorTensorTrains, leafObjects, and SSYT\[Lambda]s*)
   AncestralNestTree[EnumerateTensorProductBases,tree]
  ]


End[];


EndPackage[];
