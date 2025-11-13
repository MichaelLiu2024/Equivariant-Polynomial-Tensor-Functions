(* ::Package:: *)

(* ::Title:: *)
(*ClebschGordanTools*)


(* ::Section:: *)
(*Public Functions*)


BeginPackage["ClebschGordanTools`",{"IsotypicDecompositionTools`"}];


(* ::Subsection:: *)
(*Public Function Declarations*)


(*Ensure everything is numerical; ensure numerical results are Chopped*)


ClebschGordanPathsTensorProduct::usage="gives a list of all Clebsch-Gordan paths from \[Mu] to the tensor product of the \[Lambda]s."


ClebschGordanPathsExteriorPower::usage="gives a list of all Clebsch-Gordan paths from \[Mu] to the d-fold exterior power of \[Lambda]."


ClebschGordanPathsSymmetricPower::usage="gives a list of all Clebsch-Gordan paths from \[Mu] to the d-fold symmetric power of \[Lambda]."


ClebschGordanPathsSchurPower::usage="gives a list of all Clebsch-Gordan paths from \[Mu] to the image of the Young symmetrizer p on \[Lambda]."


ClebschGordanTensorTrain::usage="gives the tensor train representation of the Clebsch-Gordan tensor CG(\[Lambda]s,\[Gamma]s)."


EvaluateTensorTrain::usage="evaluates the tensor train representation of CG(\[Lambda]s,\[Gamma]s) at the inputs xs."


EvaluateSymmetrizedTensorTrain::usage="evaluates the symmetrized tensor train representation of CG((\[Lambda],...,\[Lambda]),\[Gamma]s) at the inputs (x,...,x)."


ClebschGordanTensor::usage="gives the Clebsch-Gordan tensor CG(\[Lambda]s,\[Gamma]s)."


AntisymmetrizedClebschGordanTensor::usage="gives the antisymmetrized Clebsch-Gordan tensor CG((\[Lambda],...,\[Lambda]),\[Gamma]s)."


EvaluateClebschGordanTensor::usage="evaluates the tensor CG(\[Lambda]s,\[Gamma]s) at the inputs xs."


(* ::Section:: *)
(*Private Functions*)


Begin["`Private`"];


(* ::Subsection:: *)
(*Private Function Implementations*)


PivotColumns=ResourceFunction["PivotColumns"];


(*a memoized numerical version of the built-in function ClebschGordan*)
ElementaryClebschGordanCoefficient[\[Lambda]1_Integer?NonNegative,m1_Integer,\[Lambda]2_Integer?NonNegative,m2_Integer,\[Lambda]3_Integer?NonNegative,m3_Integer]:=
ElementaryClebschGordanCoefficient[\[Lambda]1,m1,\[Lambda]2,m2,\[Lambda]3,m3]=
N[ClebschGordan[{\[Lambda]1,m1},{\[Lambda]2,m2},{\[Lambda]3,m3}]]


(*gives the elementary Clebsch-Gordan tensor CG({\[Lambda]1,\[Lambda]2},{\[Lambda]1,\[Gamma]2})*)
ElementaryClebschGordanTensor[\[Lambda]1_Integer?NonNegative,\[Lambda]2_Integer?NonNegative,\[Lambda]3_Integer?NonNegative]:=
ElementaryClebschGordanTensor[\[Lambda]1,\[Lambda]2,\[Lambda]3]=
Chop[
SparseArray[
Join@@Table[
{1+\[Lambda]1+m1,1+\[Lambda]2+m2,1+\[Lambda]3+m1+m2}->ElementaryClebschGordanCoefficient[\[Lambda]1,m1,\[Lambda]2,m2,\[Lambda]3,m1+m2],
{m1,-\[Lambda]1,\[Lambda]1},{m2,Max[-\[Lambda]2,-\[Lambda]3-m1],Min[\[Lambda]2,\[Lambda]3-m1]}
],
{2\[Lambda]1+1,2\[Lambda]2+1,2\[Lambda]3+1}
]
]


(*gives the coefficient of the Clebsch-Gordan tensor CG((\[Gamma]1,...,\[Gamma]1),\[Gamma]s)*)
ClebschGordanCoefficient[\[Gamma]s_List?VectorQ,ms_List?VectorQ]:=
With[
{ss=Accumulate[ms]},
Times@@MapThread[ElementaryClebschGordanCoefficient,{Most[\[Gamma]s],Most[ss],ConstantArray[First[\[Gamma]s],Length[\[Gamma]s]-1],Rest[ms],Rest[\[Gamma]s],Rest[ss]}]
]


(*contracts tensor with y in the first mode and x in the second mode*)
ContractLegs[y_?VectorQ,{x_List?VectorQ,tensor_SparseArray}]:=Dot[x,Dot[y,tensor]]


(*helper to convert indices into paths*)
\[Alpha]to\[Gamma][\[Gamma]_Integer?NonNegative,{\[Lambda]_Integer?NonNegative,\[Alpha]_Integer?NonNegative}]:=Abs[\[Gamma]-\[Lambda]]+\[Alpha]-1


(*helper*)
findIndex[acc_List?VectorQ,indices_List?VectorQ]:=Flatten[Position[acc,s_/;#<=s,1,1]&/@indices]


(* ::Subsection:: *)
(*Public Function Attributes*)


SetAttributes[
{
ClebschGordanPathsExteriorPower,
ClebschGordanPathsSymmetricPower
},
Listable
]


(* ::Subsection:: *)
(*Public Function Implementations*)


ClebschGordanPathsTensorProduct[\[Lambda]s_List?VectorQ,\[Mu]_Integer?NonNegative]:=
Map[
Function[\[Alpha]s,FoldList[\[Alpha]to\[Gamma],First[\[Lambda]s],Transpose[{Rest[\[Lambda]s],\[Alpha]s}]]],
Position[Fold[IsotypicComponentsTensorProduct,\[Lambda]s],\[Mu]]
]


ClebschGordanPathsExteriorPower[\[Lambda]_Integer?NonNegative,d_Integer?NonNegative,\[Mu]_Integer?NonNegative]/;d<=3:=
Switch[
d,
1,{{\[Lambda]}},
2,{{\[Lambda],\[Mu]}},
3,{{\[Lambda],#+1-Mod[#,2]&@Abs[\[Lambda]-\[Mu]],\[Mu]}}
];


ClebschGordanPathsSymmetricPower[\[Lambda]_Integer?NonNegative,d_Integer?NonNegative,\[Mu]_Integer?NonNegative]/;d<=3:=
Switch[
d,
1,{{\[Lambda]}},
2,{{\[Lambda],\[Mu]}},
3,{{\[Lambda],#+Mod[#,2]&@Abs[\[Lambda]-\[Mu]],\[Mu]}}
];


(*Low priority: check if this function has some analytical form*)
(*Low priority: check if random column sampling is faster*)
ClebschGordanPathsSymmetricPower[\[Lambda]_Integer?NonNegative,d_Integer?NonNegative,\[Mu]_Integer?NonNegative]/;d>=4:=
Module[
{
corePaths,coreTensorTrains,
coreRandomProbes,
syndromeMatrix,
coreIndices
},

corePaths=Select[ClebschGordanPathsTensorProduct[ConstantArray[\[Lambda],d],\[Mu]],EvenQ[#[[2]]]&];
coreTensorTrains=ClebschGordanTensorTrain[ConstantArray[\[Lambda],d]]/@corePaths;

coreRandomProbes=RandomReal[1,{d+d(*oversampling*),2\[Lambda]+1}];

syndromeMatrix=Outer[EvaluateSymmetrizedTensorTrain,coreRandomProbes,coreTensorTrains,1];

coreIndices=PivotColumns@Flatten[syndromeMatrix,{{1,3},{2}}];

corePaths[[coreIndices]]
]


ClebschGordanPathsSchurPower[\[Lambda]_Integer?NonNegative,p_List?VectorQ,\[Mu]_Integer?NonNegative]/;First[p]<=3:=
With[
{d=Total[p]},
Switch[
Length[p](*number of parts*),
1,{#,{\[Mu]}}&/@ClebschGordanPathsExteriorPower[\[Lambda],d,\[Mu]],
d,{\[Xi]\[Lambda]ps(*How to get these? we may need to return these in the original function CGPathsSymmetricPower... although this is somewhat undesirable*),#}&/@ClebschGordanPathsSymmetricPower[\[Lambda],d,\[Mu]],
_,ClebschGordanPathsSchurPower[\[Lambda],p,\[Mu]]
]
]


ClebschGordanPathsSchurPower[\[Lambda]_Integer?NonNegative,p_List?VectorQ,\[Mu]_Integer?NonNegative]/;First[p]<=3\[And]1<Length[p]<Total[p]:=
Module[
{
coreLegs,corePaths,coreTensorTrains,
leafPaths,leafTensors,
leafRandomProbes,coreRandomProbes,
syndromeMatrix,
coreIndices,leafIndices,
d=Total[p]
},

coreLegs=Select[Tuples@IsotypicComponentsExteriorPower[\[Lambda],p],IsotypicComponentTensorProductQ[#,\[Mu]]&];
corePaths=ClebschGordanPathsTensorProduct[#,\[Mu]]&/@coreLegs;
coreTensorTrains=MapThread[ClebschGordanTensorTrain[#1]/@#2&,{coreLegs,corePaths}];

leafPaths=ClebschGordanPathsExteriorPower[\[Lambda],p,#]&/@coreLegs;
leafTensors=Map[AntisymmetrizedClebschGordanTensor,leafPaths,{3}];

leafRandomProbes=RandomReal[1,{d+d(*oversampling*),First[p],2\[Lambda]+1}];
coreRandomProbes=Outer[EvaluateClebschGordanTensor,leafRandomProbes,leafTensors,1,3];

(*When First[p]\[LessEqual]3, the subselection below is simple. In general, we would need to take Tuples, and the bookkeeping gets even more complicated.*)
coreRandomProbes=Flatten[coreRandomProbes,{{1},{2},{3,4}}];

(*This is unclean but acceptable*)
syndromeMatrix=
MapThread[
Function[
{coreRandomProbe,coreTensorTrain},
EvaluateTensorTrain[coreRandomProbe,#]&/@coreTensorTrain
],
{#,coreTensorTrains}
]&/@coreRandomProbes;

coreIndices=PivotColumns@Flatten[syndromeMatrix,{{1,4},{2,3}}];
leafIndices=findIndex[Accumulate[Length/@corePaths],coreIndices];

Transpose[{Flatten[leafPaths,{{1},{2},{3,4}}][[leafIndices]],Flatten[corePaths,1][[coreIndices]]}]
]


ClebschGordanTensorTrain[\[Lambda]s_List?VectorQ][\[Gamma]s_List?VectorQ]:=ClebschGordanTensorTrain[\[Lambda]s,\[Gamma]s]
ClebschGordanTensorTrain[\[Lambda]s_List?VectorQ,\[Gamma]s_List?VectorQ]:=MapThread[ElementaryClebschGordanTensor,{Most[\[Gamma]s],Rest[\[Lambda]s],Rest[\[Gamma]s]}]


EvaluateTensorTrain[xs_List,tt_List]:=Chop@Fold[ContractLegs,First[xs],Transpose[{Rest[xs],tt}]]


EvaluateSymmetrizedTensorTrain[x_List?VectorQ,tt_List]:=EvaluateTensorTrain[ConstantArray[x,Length[tt]+1],tt]


(*Maybe this should take the tensor train as input?*)
ClebschGordanTensor[\[Lambda]s_List?VectorQ][\[Gamma]s_List?VectorQ]:=ClebschGordanTensor[\[Lambda]s,\[Gamma]s]
ClebschGordanTensor[\[Lambda]s_List?VectorQ,\[Gamma]s_List?VectorQ]:=
If[
Length[\[Lambda]s]==1,(*we should remove calls with length 1 eventually by adjusting code higher up*)
IdentityMatrix[2First[\[Gamma]s]+1,SparseArray],
Chop@Dot@@ClebschGordanTensorTrain[\[Lambda]s,\[Gamma]s]
]


(*Explicitly implement the case length=3 as well. When done, separate into length <=3 and length >=4 cases for clarity*)
AntisymmetrizedClebschGordanTensor[\[Gamma]s_List?VectorQ]/;Length[\[Gamma]s]<=3:=
Switch[
Length[\[Gamma]s],
1,IdentityMatrix[2First[\[Gamma]s]+1,SparseArray],
2,If[EvenQ[\[Gamma]s[[2]]],0,ClebschGordanTensor[ConstantArray[First[\[Gamma]s],2],\[Gamma]s]],
_,Module[
{\[Lambda]=First[\[Gamma]s],\[Mu]=Last[\[Gamma]s],d=Length[\[Gamma]s],msList,\[Lambda]s\[Mu]},

(*We could still try to generate these directly somehow...*)
msList=Select[Permutations[Range[-\[Lambda],\[Lambda]],{d}],-\[Gamma]s\[VectorLessEqual]Accumulate[#]\[VectorLessEqual]\[Gamma]s&];
\[Lambda]s\[Mu]=Append[ConstantArray[\[Lambda],d],\[Mu]];

Chop[
Symmetrize[
SymmetrizedArray[
1+\[Lambda]s\[Mu]+Append[#,Total[#]]->ClebschGordanCoefficient[\[Gamma]s,#]&/@msList,
2\[Lambda]s\[Mu]+1
],
Antisymmetric[Range[d]]
]
]
]
]


EvaluateClebschGordanTensor[xs_List,tensor_]:=Chop@Normal@Fold[Dot[#2,#1]&,tensor,Take[xs,TensorRank[tensor]-1]]


End[];


EndPackage[];
