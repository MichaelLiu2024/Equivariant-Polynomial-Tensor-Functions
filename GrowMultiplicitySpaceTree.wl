(* ::Package:: *)

BeginPackage["GrowMultiplicitySpaceTree`",{"TensorTools`","ClebschGordanTools`","IsotypicDecompositionTools`","CombinatoricsTools`"}];


IsotypicDataTree
EnumerateVectorSpaceBases


Begin["`Private`"];


PruneChildlessNodes[tree_Tree]:=TreeFold[If[#2=={},Nothing,Tree[##]]&,tree]


AncestralNestTree[f_,tree_Tree]:=
 TreeReplacePart[
  tree,
  Function[
   pos,
   pos:>Tree[
    TreeExtract[tree,pos,TreeData],
    Tree[#,None]&/@f[TreeExtract[tree,Take[pos,#]&/@Range[0,Length@pos],TreeData]]
   ]
  ]/@TreePosition[tree,_,"Leaves"]
 ]


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


HarmonicTensorCoordinates[l_Integer?NonNegative,m_Integer]:=HarmonicTensorCoordinates[l,m]=
 Total@ReplaceAll[
  CoefficientRules[SolidHarmonicR[l,m,x,y,z],{x,y,z}],
  (powers_->coefficients_):>coefficients*Global`x[Join@@MapThread[ConstantArray,{Range[3],powers}]]
 ]


(*This and any other FullSimplify will take up a lot of time! But it is only a one-time cost, and simplifications here will make the final evaluation faster*)
SphericalBasisToMonomialBasis[sphericalPolynomials_]:=
 ReplaceAll[
  Chop@Expand@ReplaceAll[
   sphericalPolynomials,
   Global`x[l_][m_][mult_]:>(HarmonicTensorCoordinates[l,m]/.Global`x[p_]:>Global`x[p][mult])
  ],
  r:(_Real|_Complex):>RootApproximant[r]
 ]


SetAttributes[generateVariables,Listable]
generateVariables[\[Lambda]_Integer?NonNegative,mult_Integer?Positive]:=Table[Global`x[\[Lambda]][m][n],{n,1,mult},{m,-\[Lambda],\[Lambda]}]


EvaluatePolynomials[bases_Association,variables_List]:=
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

  sphericalPolynomials=Flatten[Outer[EvaluateTensorTrain,bases[["interiorTensorTrains"]],Tuples@interiorVectors,1],1];
  SphericalBasisToMonomialBasis[sphericalPolynomials]
 ]


EvaluateIsotypicDataTree[tree_Tree]:=
 EvaluatePolynomials[#,generateVariables[Sequence@@Most@TreeData@tree]]&/@TreeData/@TreeLeaves@tree


degree[p_]:=Total@Exponent[First@p,Variables[First@p]]


EnumerateVectorSpaceBases[\[Lambda]s_List,m\[Lambda]s_List,\[Nu]_Integer?NonNegative,DMax_Integer?Positive]/;
 SO3RepresentationQ[\[Lambda]s,m\[Lambda]s]:=
  GatherBy[
   SortBy[
    Flatten@MapThread[
     EvaluateIsotypicDataTree@IsotypicDataTree[##,\[Nu],DMax]&,
     {Subsets[\[Lambda]s,{1,\[Infinity]}],Subsets[m\[Lambda]s,{1,\[Infinity]}]}
    ],
    degree
   ],
   degree
  ]


(* ::Subsection:: *)
(*Public Function Implementations*)


(*Write a function to take permutations of multiplicities and substitute labels.*)
(*Then, write a function to multiply all lower degree invariants and do pivot finding to get independent higher degree invariants. you can do simple checks like toss out zeros, and if there is nothing left, you are already done!*)


SO3RepresentationQ[\[Lambda]s_List,m\[Lambda]s_List]:=
 VectorQ[\[Lambda]s,Positive]\[And]
 VectorQ[m\[Lambda]s,Positive]\[And]
 Length[\[Lambda]s]==Length[m\[Lambda]s]\[And]
 DuplicateFreeQ[\[Lambda]s]


IsotypicDataTree::usage="forms the isotypic data tree"
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
   
   If[tree==Nothing,Return[Tree[{\[Lambda]s,m\[Lambda]s,\[Nu]},{}]]];
   
   (*Level 5: interiorTensorTrains, leafObjects, and SSYT\[Lambda]s*)
   AncestralNestTree[EnumerateTensorProductBases,tree]
  ]


End[];


EndPackage[];
