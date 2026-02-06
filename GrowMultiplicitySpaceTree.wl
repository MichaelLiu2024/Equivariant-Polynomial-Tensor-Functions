(* ::Package:: *)

(* ::Section:: *)
(*To Do*)


(*We could try an alternative implementation of IsotypicMultiplicitySchurPower: find an explicit expression for the generating function of the number of
semistandard Young tableaux (SSYT) of shape p with powers being the total sum of entries and use Coefficient. Maybe try this for IsotypicMultiplicityExteriorPower
as well for consistency, though tbh it may be slower. Low priority though.*)
(*Replace Tuples with Sequence; need to adjust the pure function ContractTensorTree*)
(*We will have another layer over all 0\[VectorLessEqual]m\[Lambda]s\[VectorLessEqual]m\[Lambda]sMax, restricting the \[Lambda]s appropriately, etc. each calls IsotypicDataTree*)


BeginPackage["GrowMultiplicitySpaceTree`",{"TensorTools`","ClebschGordanTools`","IsotypicDecompositionTools`","CombinatoricsTools`"}];


IsotypicDataTree::usage="forms the isotypic data tree"


Begin["`Private`"];


(* ::Subsubsection:: *)
(*Private Functions*)


(*recursively prunes childless nodes from the input tree*)
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
   "leafObjects"->MapThread[TensorTrainBasisSchurPower,{\[Lambda]s,\[Pi]\[Lambda]s,\[Mu]\[Lambda]s}],
   "SSYT\[Lambda]s"->MapThread[SemiStandardYoungTableaux,{\[Pi]\[Lambda]s,m\[Lambda]s}]
  |>
 }


(* ::Subsubsection:: *)
(*IsotypicDataTreeToPolynomials*)


(*https://resources.wolframcloud.com/FunctionRepository/resources/SolidHarmonicR/*)
SolidHarmonicR[l_Integer?NonNegative,m_Integer,x_,y_,z_]/;Abs[m]<=l:=
 With[
  {dpower=If[#2==0,1,#1^#2]&,s=Sign[m],am=Abs[m]},
  
  (-1)^((1-s)am/2)Sqrt[(l-am)!/(l+am)!]dpower[x+I s y,am]*
  Sum[
   (-1)^((l+am)/2-k)(l+am+2k-1)!!dpower[z,2k]dpower[x^2+y^2+z^2,(l-am)/2-k]/((2k)!(l-am-2k)!!),
   {k,Mod[l-am,2]/2,(l-am)/2},
   Method->"Procedural"
  ]
 ]


SphericalBasisToMonomialBasis[sphericalPolynomials_]:=
 FullSimplify@ReplaceAll[
  Chop@FullSimplify@ReplaceAll[
   sphericalPolynomials,
   Subscript[Global`x,l_,m_,mult_]:>ReplaceAll[Expand@SolidHarmonicR[l,m,x,y,z],Times@@({x,y,z}^#)->Subscript[Global`x,mult,Join@@MapThread[ConstantArray,{Range[3],#}]]&/@WeakCompositions[l,3]]
  ],
  r:(_Real|_Complex):>RootApproximant[r]
 ]


SetAttributes[generateVariables,Listable]
generateVariables[\[Lambda]_Integer?NonNegative,mult_Integer?Positive]:=Table[Subscript[Global`x,\[Lambda],m,n],{n,1,mult},{m,-\[Lambda],\[Lambda]}]


EvaluatePolynomials[{{\[Lambda]s_,m\[Lambda]s_,\[Nu]_},D_,d\[Lambda]s_,\[Pi]\[Lambda]s_,\[Mu]\[Lambda]s_,assoc_}]:=
 Module[
  {
   inputVariables,
   leafVariables,
   
   leafTensors,leafVectors,
   sphericalPolynomials
  },
  
  inputVariables=generateVariables[\[Lambda]s,m\[Lambda]s];
  leafVariables=SymmetricMonomialCP[x];

  (*Temporary solution; replace with polarization*)
  leafTensors=Map[ContractLeafTensorsCoreTensorTrain[Sequence@@#]&,assoc[["leafObjects"]],{2}];
  leafTensors=MapThread[SymmetrizeColumns[#1]/@#2&,{\[Pi]\[Lambda]s,leafTensors}];

  leafVectors=MapThread[Flatten[Outer[ContractLeafSSYTCoreTensor,##,1],1]&,{assoc[["SSYT\[Lambda]s"]],leafTensors}];

  sphericalPolynomials=Flatten[Outer[ContractLeafVectorsCoreTensorTrain,Tuples[leafVectors],assoc[["interiorTensorTrains"]],1],1];
  SphericalBasisToMonomialBasis[sphericalPolynomials]
 ]


(* ::Subsection:: *)
(*Public Function Implementations*)


SO3RepresentationQ[\[Lambda]s_List,m\[Lambda]s_List]:=
 VectorQ[\[Lambda]s,Positive]\[And]
 VectorQ[m\[Lambda]s,Positive]\[And]
 Length[\[Lambda]s]==Length[m\[Lambda]s]\[And]
 DuplicateFreeQ[\[Lambda]s]


IsotypicDataTree[\[Lambda]s_List,m\[Lambda]s_List,\[Nu]_Integer?NonNegative,DMax_Integer?Positive]/;
 SO3RepresentationQ[\[Lambda]s,m\[Lambda]s]\[And]
 Total[m\[Lambda]s]<=DMax:=
  Module[
   {tree},
   
   (*Level 1: D*)
   tree=Tree[{\[Lambda]s,m\[Lambda]s,\[Nu]},Range[Total[m\[Lambda]s],DMax]];
   
   (*Level 2: d\[Lambda]s*)
   tree=NestTree[Select[StrictCompositions[#,Length[\[Lambda]s]],m\[Lambda]s\[VectorLessEqual]#&]&,tree];
   
   (*Level 3: \[Pi]\[Lambda]s*)
   tree=NestTree[Tuples@ThinPartitions[#,\[Lambda]s,m\[Lambda]s]&,tree];
   
   (*Level 4: \[Mu]\[Lambda]s*)
   tree=NestTree[ConstrainedIsotypicComponentsSchurPowers[\[Lambda]s,#,\[Nu]]&,tree];
   
   (*Prune childless nodes for memory efficiency*)
   tree=PruneChildlessNodes[tree];
   
   (*Level 5: interiorTensorTrains, leafObjects, and SSYT\[Lambda]s*)
   tree=AncestralNestTree[EnumerateTensorProductBases,tree];
   
   (*Level 6: polynomials*)
   tree=AncestralNestTree[EvaluatePolynomials,tree]
  ]


End[];


EndPackage[];
