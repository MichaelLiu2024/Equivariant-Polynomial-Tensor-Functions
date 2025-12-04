(* ::Package:: *)

(* ::Section:: *)
(*Public Functions*)


BeginPackage["GrowMultiplicitySpaceTree`",{"TensorTools`","ClebschGordanTools`","IsotypicDecompositionTools`","CombinatoricsTools`"}];


(* ::Subsection:: *)
(*Public Function Declarations*)


(*SchurS -> Det is the only bottleneck. Symbolic determinant of a matrix with polynomial entries*)
(*We could try an alternative implementation of IsotypicMultiplicitySchurPower: find an explicit expression for the generating function of the number of
semistandard Young tableaux (SSYT) of shape p with powers being the total sum of entries and use Coefficient. Maybe try this for IsotypicMultiplicityExteriorPower
as well for consistency, though tbh it may be slower. Low priority though.*)
(*USE MATLAB squeeze in Mathematica via ArrayReshape and Dimensions (or something else) to remove modes of dimension 1*)
(*Apply identity matrices implicitly; don't form them as sparse arrays and multiply,this is a waste*)
GrowMultiplicitySpaceTree::usage="returns the tree"


(* ::Section:: *)
(*Private Functions*)


Begin["`Private`"];


(* ::Subsection:: *)
(*Private Function Implementations*)


MuTuples[\[Lambda]s_List?VectorQ,\[Pi]\[Lambda]s_List,\[Nu]_Integer?NonNegative]:=Select[Tuples@MapThread[IsotypicComponentsSchurPower,{\[Lambda]s,\[Pi]\[Lambda]s}],IsotypicComponentTensorProductQ[#,\[Nu]]&]


PruneChildlessNodes[tree_]:=TreeFold[If[#2=={},Nothing,Tree[##]]&,tree]


SchurPathToTensorTrain[{leafPaths_List,corePath_List?VectorQ}]:=
{AntisymmetrizedClebschGordanTensor/@leafPaths,ClebschGordanTensorTrain[Last/@leafPaths,corePath]}


SolidHarmonicR=ResourceFunction["SolidHarmonicR"];


SphericalBasisToMonomialBasis[sphericalPolynomials_]:=
Flatten@FullSimplify@ReplaceAll[
Chop@FullSimplify@ReplaceAll[
sphericalPolynomials,
Subscript[Global`x,\[Lambda]_,vec_,mult_]:>SolidHarmonicR[\[Lambda],vec,Subscript[Global`x,mult],Subscript[Global`y,mult],Subscript[Global`z,mult]]
],
r:(_Real|_Complex):>RootApproximant[r]
]


HarvestPath[{{\[Lambda]s_,m\[Lambda]s_,\[Nu]_},D_,d\[Lambda]s_,\[Pi]\[Lambda]s_,\[Mu]\[Lambda]s_}]:=
Module[
{
SSYT\[Lambda]s,
corePaths,coreTensorTrains,
leafPaths,leafTensorTrees,
leafTensors,
coreProbes,
sphericalPolynomials
},

SSYT\[Lambda]s=MapThread[SemiStandardYoungTableaux,{\[Pi]\[Lambda]s,m\[Lambda]s}];

corePaths=ClebschGordanPathsTensorProduct[\[Mu]\[Lambda]s,\[Nu]];
coreTensorTrains=ClebschGordanTensorTrain[\[Mu]\[Lambda]s]/@corePaths;

leafPaths=MapThread[ClebschGordanPathsSchurPower,{\[Lambda]s,\[Pi]\[Lambda]s,\[Mu]\[Lambda]s}];
leafTensorTrees=Map[SchurPathToTensorTrain,leafPaths,{2}];

(*Temporary solution; replace with polarization*)
leafTensors=Map[ContractLeafTensorsCoreTensorTrain[Sequence@@#]&,leafTensorTrees,{2}];
leafTensors=MapThread[SymmetrizeColumns[#1]/@#2&,{\[Pi]\[Lambda]s,leafTensors}];

coreProbes=MapThread[Flatten[Outer[ContractLeafSSYTCoreTensor,##,1],1]&,{SSYT\[Lambda]s,leafTensors}];

(*Outer[Print@*SpinListToSpinTree@*List,Tuples[leafPaths],corePaths,1];Rewrite this function to work on tensor trains, not paths*)
(*Replace Tuples with Sequence; need to adjust the pure function ContractTensorTree*)
(*Let's go back to ClebschGordanPathsSchurPower and use our new understanding of Outer to write the most generalized code.*)
(*
{<|"Subscript[Hom, G](Subscript[H, \[Nu]],Underscript[\[CircleTimes], \[Lambda]]Subscript[H, Subscript[\[Mu], \[Lambda]]])"->coreTensorTrees,"(Subscript[Hom, G](Subscript[H, Subscript[\[Mu], \[Lambda]]],Subscript[e, Subscript[\[Pi], \[Lambda]]](Subsuperscript[H, \[Lambda], \[CircleTimes]Subscript[d, \[Lambda]]])Subscript[), \[Lambda]]"->leafTensorTrees|>};*)

sphericalPolynomials=Flatten[Outer[ContractLeafVectorsCoreTensorTrain,Tuples[coreProbes],coreTensorTrains,1],1];
SphericalBasisToMonomialBasis[sphericalPolynomials]
]


AncestralNestTree[f_,tree_]:=
TreeReplacePart[
tree,
Function[
pos,
pos:>Tree[
TreeExtract[tree,pos,TreeData],
Tree[#,None]&/@f[TreeExtract[tree,Take[pos,#]&/@Range[0,Length@pos],TreeData]]
]
]/@TreePosition[tree,_,"Leaves"],
ImageSize->Large
]


(* ::Subsection:: *)
(*Public Function Implementations*)


GrowMultiplicitySpaceTree[\[Lambda]s_,m\[Lambda]s_,\[Nu]_,Ds_]:=
Module[
{tree},

(*Level 1: D*)
tree=Tree[{\[Lambda]s,m\[Lambda]s,\[Nu]},Ds];

(*Level 2: d\[Lambda]s*)
tree=NestTree[StrictCompositions[#,Length[\[Lambda]s]]&,tree];

(*Level 3: \[Pi]\[Lambda]s*)
tree=NestTree[Tuples@ThinPartitions[#,\[Lambda]s,m\[Lambda]s]&,tree];

(*Level 4: \[Mu]\[Lambda]s*)
tree=NestTree[MuTuples[\[Lambda]s,#,\[Nu]]&,tree];

(*Prune childless nodes for memory efficiency*)
tree=PruneChildlessNodes[tree];

AncestralNestTree[HarvestPath,tree]
]


End[];


EndPackage[];
