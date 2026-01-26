(* ::Package:: *)

(* ::Section:: *)
(*To Do*)


(*SchurS -> Det is one bottleneck in IsotypicDataTree. Symbolic determinant of a matrix with polynomial entries*)
(*We could try an alternative implementation of IsotypicMultiplicitySchurPower: find an explicit expression for the generating function of the number of
semistandard Young tableaux (SSYT) of shape p with powers being the total sum of entries and use Coefficient. Maybe try this for IsotypicMultiplicityExteriorPower
as well for consistency, though tbh it may be slower. Low priority though.*)
(*USE MATLAB squeeze in Mathematica via ArrayReshape and Dimensions (or something else) to remove modes of dimension 1*)
(*Apply identity matrices implicitly; don't form them as sparse arrays and multiply,this is a waste*)
(*Replace Tuples with Sequence; need to adjust the pure function ContractTensorTree*)
(*Let's go back to ClebschGordanPathsSchurPower and use our new understanding of Outer to write the most generalized code.*)


BeginPackage["GrowMultiplicitySpaceTree`",{"TensorTools`","ClebschGordanTools`","IsotypicDecompositionTools`","CombinatoricsTools`"}];


IsotypicDataTree::usage="forms the isotypic data tree"
IsotypicDataTreeToPolynomials::usage="converts the isotypic data tree into the corresponding list of equivariant polynomials"


Begin["`Private`"];


(* ::Subsubsection:: *)
(*Private Functions*)


CoreSpins[\[Lambda]s_List?VectorQ,\[Pi]\[Lambda]s_List,\[Nu]_Integer?NonNegative]:=
 If[
  Length@\[Lambda]s==1\[And]\[Nu]==0\[And]IsotypicMultiplicitySchurPower[First@\[Lambda]s,First@\[Pi]\[Lambda]s,0]>0,
  {{0}},
  Select[
   Tuples@DeleteCases[MapThread[IsotypicComponentsSchurPower,{\[Lambda]s,\[Pi]\[Lambda]s}],0,All],(*algebra generation constraint*)
   IsotypicComponentTensorProductQ[#,\[Nu]]&
  ]
 ]


ThinPartitions::usage="gives a list of all integer partitions of d with parts at most Min[2\[Lambda]+1,m]"
SetAttributes[ThinPartitions,Listable]
ThinPartitions[d\[Lambda]_Integer?NonNegative,\[Lambda]_Integer?NonNegative,m\[Lambda]_Integer?Positive]:=IntegerPartitions[d\[Lambda],All,Range[Min[2\[Lambda]+1,m\[Lambda]]]]


PruneChildlessNodes[tree_Tree]:=TreeFold[If[#2=={},Nothing,Tree[##]]&,tree]


PathsSSYTs[{{\[Lambda]s_,m\[Lambda]s_,\[Nu]_},D_,d\[Lambda]s_,\[Pi]\[Lambda]s_,\[Mu]\[Lambda]s_}]:=
 With[
  {
   corePaths=ClebschGordanPathsTensorProduct[\[Mu]\[Lambda]s,\[Nu]],
   leafPaths=MapThread[ClebschGordanPathsSchurPower,{\[Lambda]s,\[Pi]\[Lambda]s,\[Mu]\[Lambda]s}],
   SSYT\[Lambda]s=MapThread[SemiStandardYoungTableaux,{\[Pi]\[Lambda]s,m\[Lambda]s}]
  },
  If[
   MemberQ[leafPaths,{}],
   {},
   {
    <|
     "corePaths"->corePaths,
     "leafPaths"->leafPaths,
     "SSYT\[Lambda]s"->SSYT\[Lambda]s
    |>
   }
  ]
 ]


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


(* ::Subsubsection:: *)
(*IsotypicDataTreeToPolynomials*)


PathTreeToTensorTree[{leafPaths_List,corePath_List?VectorQ}]:=
 {
  AntisymmetrizedClebschGordanTensor/@leafPaths,
  ClebschGordanTensorTrain[Last/@leafPaths,corePath]
 }


(*https://resources.wolframcloud.com/FunctionRepository/resources/SolidHarmonicR/*)
SolidHarmonicR[l_Integer?NonNegative,m_Integer,x_,y_,z_]/;Abs[m]<=l:=
 With[
  {dpower=If[#2==0,1,#1^#2]&,s=Sign[m],am=Abs[m]},
  
  (-1)^((1-s)am/2)Sqrt[(l-am)!/(l+am)!]dpower[x+I s y,am]
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


PathsSSYTsToPolynomials[assoc_Association]:=
 Module[
  {
   \[Mu]\[Lambda]s,
   \[Pi]\[Lambda]s,
   coreTensorTrains,
   leafTensorTrees,leafTensors,leafVectors,
   sphericalPolynomials
  },

  \[Mu]\[Lambda]s=First@*Last@*First@*First/@assoc[["leafPaths"]];
  \[Pi]\[Lambda]s=Length/@First[#]&/@assoc[["SSYT\[Lambda]s"]];

  coreTensorTrains=ClebschGordanTensorTrain[\[Mu]\[Lambda]s]/@assoc[["corePaths"]];

  leafTensorTrees=Map[PathTreeToTensorTree,assoc[["leafPaths"]],{2}];

  (*Temporary solution; replace with polarization*)
  leafTensors=Map[ContractLeafTensorsCoreTensorTrain[Sequence@@#]&,leafTensorTrees,{2}];
  leafTensors=MapThread[SymmetrizeColumns[#1]/@#2&,{\[Pi]\[Lambda]s,leafTensors}];

  leafVectors=MapThread[Flatten[Outer[ContractLeafSSYTCoreTensor,##,1],1]&,{assoc[["SSYT\[Lambda]s"]],leafTensors}];

  sphericalPolynomials=Flatten[Outer[ContractLeafVectorsCoreTensorTrain,Tuples[leafVectors],coreTensorTrains,1],1];
  SphericalBasisToMonomialBasis[sphericalPolynomials]
 ]


(* ::Subsection:: *)
(*Public Function Implementations*)


IsotypicDataTree[\[Lambda]s_List?VectorQ,m\[Lambda]s_List?VectorQ,\[Nu]_Integer?NonNegative,dMax_Integer?Positive]/;
 Length[\[Lambda]s]==Length[m\[Lambda]s]\[And]Total[m\[Lambda]s]<=dMax:=
 Module[
  {tree},

  (*Level 1: D*)
  tree=Tree[{\[Lambda]s,m\[Lambda]s,\[Nu]},Range[Total[m\[Lambda]s],dMax]];

  (*Level 2: d\[Lambda]s*)
  tree=NestTree[Select[StrictCompositions[#,Length[\[Lambda]s]],m\[Lambda]s\[VectorLessEqual]#&]&,tree];

  (*Level 3: \[Pi]\[Lambda]s*)
  tree=NestTree[Tuples@ThinPartitions[#,\[Lambda]s,m\[Lambda]s]&,tree];

  (*Level 4: \[Mu]\[Lambda]s*)
  tree=NestTree[CoreSpins[\[Lambda]s,#,\[Nu]]&,tree];

  (*Prune childless nodes for memory efficiency*)
  tree=PruneChildlessNodes[tree];

  (*Level 5: path bases and SSYT bases*)
  tree=AncestralNestTree[PathsSSYTs,tree];
  
  PruneChildlessNodes[tree]
 ]


IsotypicDataTreeToPolynomials[tree_Tree]:=Flatten[PathsSSYTsToPolynomials/@TreeData/@TreeLeaves@tree]


End[];


EndPackage[];
